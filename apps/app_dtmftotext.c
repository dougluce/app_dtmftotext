/*
 * Asterisk -- A telephony toolkit for Linux.
 *
 * Text entry by DTMF
 * 
 * Copyright (C) 2012, Doug Luce
 * Copyright (C) 2003, Steve Underwood
 *
 * Steve Underwood <steveu@coppice.org>
 *
 * This program is free software, distributed under the terms of
 * the GNU General Public License
 */

#include <sys/types.h>
#include <stdio.h>
#include "asterisk.h"
#include "asterisk/file.h"
#include "asterisk/logger.h"
#include "asterisk/channel.h"
#include "asterisk/pbx.h"
#include "asterisk/module.h"
#include "asterisk/pbx.h"
#include "asterisk/md5.h"
#include "asterisk/config.h"
#include <ctype.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <stdint.h>
#include <sys/socket.h>
#include <netdb.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <pthread.h>
#include <tiffio.h>

#define PRE_DIGIT_TIMEOUT   (8000*5)
#define INTER_DIGIT_TIMEOUT (8000*3/2)
#define LOG_DEBUGG LOG_WARNING

static char *descrip =
"  DTMFToText(variable=initial digits|max chars|max time): Assigns a string\n"
"entered by someone, using DTMF.\n"
"\n"
"This provides functionality somewhat like text entry on a cellphone, but\n"
"works for any DTMF phone. It does not depend on the timing of the key taps, as\n"
"cellphones do. This would cause serious problems when the sending phone generates\n"
"DTMF, with timing completely isolated from the user's tapping of the keys (PBXs with\n"
"digital phones, cell phones to land lines, and other situations are generally like\n"
"this.\n"
"\n"
"Initially input is in numeric mode. The '*' and '#' keys are used to alter\n"
"the entry mode from that point, to permit full entry of English (or any\n"
"other Romance language that does not demand accents).\n"
"\n"
"'**X' changes mode, or backspaces. The valid values for 'X' are as follows:\n"
"\n"
"'**2' (C) backspaces a character\n"
"'**5' (L) selects lower case input\n"
"'**6' (N) selects numeric input\n"
"'**7' (P/S) selects punctuation/symbols\n"
"'**8' (U) selects upper case input\n"
"'**9' (W) backspaces a word\n"
"'**#' Read back message to date and continue entry\n"
"\n"
"When in alpha entry mode, characters are entered by multiple presses of the\n"
"numeric digit labelled with the required character. This is similar to text\n"
"entry on most cellphones.\n"
"'*' is a break point between characters, if it is not followed by a second '*'\n"
"'#' on its own terminates input\n"
"\n"
"In alpha mode, characters may be entered as follows:\n"
"0     ,    00    .    000   ?    0000  0\n"
"1     !    11    :    111   ;    1111  #    11111 1\n"
"2     A    22    B    222   C    2222  2\n"
"3     D    33    E    333   F    3333  3\n"
"4     G    44    H    444   I    4444  4\n"
"5     J    55    K    555   L    5555  5\n"
"6     M    66    N    666   O    6666  6\n"
"7     P    77    Q    777   R    7777  S    77777 7\n"
"8     T    88    U    888   V    8888  8\n"
"9     W    99    X    999   Y    9999  Z    99999 9\n"
"\n"
"In symbol mode, characters may be entered as follows:\n"
"0     =\n"
"1     <    11    (    111   [    1111  {    11111 1\n"
"2     @    22    $    222   &    2222  %    22222 2\n"
"3     >    33    )    333   ]    3333  }    33333 3\n"
"4     +    44    -    444   *    4444  /    44444 4\n"
"5     '    55    `    555   5\n"
"6     \"    66    6\n"
"7     ^    77    7\n"
"8     \\    88    |    888   8\n"
"9     _    99    ~    999   9\n";

static char *app = "DTMFToText";

static char *synopsis = "Text entry, by DTMF, to a given variable";

/* Makes words out of punctuation, to help TTS do a reasonable job of reading back the
   enetered text. */

static const char *char_to_text(char c)
{
    char *s;
    
    s = NULL;
    switch (c)
    {
    case ' ':
        s = "space";
        break;
    case '.':
        s = "period";
        break;
    case ',':
        s = "comma";
        break;
    case '!':
        s = "exclamation mark";
        break;
    case '?':
        s = "question mark";
        break;
    case '@':
        s = "\"at\" sign";
        break;
    }
    /*endswitch*/
    return  s;
}

enum
{
    TEXT_ENTRY_MODE_LOWER_CASE,
    TEXT_ENTRY_MODE_UPPER_CASE,
    TEXT_ENTRY_MODE_NUMERIC,
    TEXT_ENTRY_MODE_SYMBOL
};

static int get_input_text(struct ast_channel *chan, const char *variable_name, const char *initial_digits, int max_chars, int max_time)
{
    static const char *uclc_presses[10] =
    {
        " ,.?0",
        "!:;#1",
        "ABC2",
        "DEF3",
        "GHI4",
        "JKL5",
        "MNO6",
        "PQRS7",
        "TUV8",
        "WXYZ9"
    };
    static const char *symbol_presses[10] =
    {
        "=0",
        "<([{1",
        "@$&%2",
        ">)]}3",
        "+-*/4",
        "'`5",
        "\"6",
        "^7",
        "\\|8",
        "_~9"
    };
    int res;
    int fest_res;
    int mode;
    int len;
    int hits;
    int i;
    int done;
    int total_timer;
    int timer;
    int digits;
    char *s;
    char *t;
    char *u;
    char *ul;
    char *v;
    const char *q;
    const char *r;
    char x;
    char digval[128 + 1];
    char talk_back[1000 + 1];
    char entered_text[500 + 1];
    struct ast_frame *f;
    struct ast_format original_read_fmt;

    len = 0;
    t = entered_text;
    done = 0;
    mode = TEXT_ENTRY_MODE_LOWER_CASE;
    res = -1;
    fest_res = -1;
    timer = PRE_DIGIT_TIMEOUT;
    total_timer = 8000*max_time;
    digits = 0;
    if (initial_digits  &&  initial_digits[0])
    {
        strcpy(digval, initial_digits);
        digits = strlen(digval);
    }
    else
    {
        digval[0] = '\0';
        digits = 0;
    }
    /*endif*/

    ast_format_copy(&original_read_fmt, ast_channel_readformat(chan));
    if (original_read_fmt.id != AST_FORMAT_SLINEAR)
    {
        res = ast_set_read_format_by_id(chan, AST_FORMAT_SLINEAR);
        if (res < 0)
        {
            ast_log(LOG_WARNING, "Unable to set to linear read mode, giving up\n");
            return -1;
        }
        /*endif*/
    }
    /*endif*/
    while (!done  &&  ast_waitfor(chan, -1) > -1)
    {
        f = ast_read(chan);
        if (f == NULL)
        {
            ast_log(LOG_WARNING, "Null frame == hangup() detected\n");
            res = -1;
            ast_frfree(f);
            break;
        }
        /*endif*/
        if (f->frametype == AST_FRAME_DTMF)
        {
	    char c = (char) f->subclass.integer;
	    ast_log(LOG_DEBUGG, "User pressed '%c'\n", c);
	    digval[digits++] = c;
	    digval[digits] = '\0';
            if (c != '#')
            {
                /* Use a shorter timeout between digits */
                timer = INTER_DIGIT_TIMEOUT;
                ast_frfree(f);
                continue;
            }
            /*endif*/
        }
        else
        {
                ast_frfree(f);
		ast_log(LOG_DEBUG, "Non-DTMF frame\n");
                continue;
        }
        /*endif*/
        timer = PRE_DIGIT_TIMEOUT;
        ast_frfree(f);

        ast_log(LOG_WARNING, "Fresh digits '%s'\n", digval);
        if (digval[0] == '\0')
            break;
        /*endif*/
        
        /* Even if the caller hung up we may still have a valid input, as it
           is often valid to enter a string of digits at the last phase of a
           call and just drop the line */
        ast_log(LOG_DEBUGG, "Current text %d/%d\n", (int)(t - entered_text), max_chars);
        s = digval;
        ul =
        u = talk_back;
        while (*s  &&  !done)
        {
            x = *s++;
            hits = 1;
            while (*s == x)
            {
                s++;
                hits++;
            }
            /*endwhile*/
            ast_log(LOG_DEBUGG, "%d of %c\n", hits, x);
            if (x == '*')
            {
                switch (hits)
                {
                case 1:
                    /* This is just a break marker, so ignore it */
                    ast_log(LOG_DEBUGG, "Marker - ignore\n");
                    break;
                case 2:
                    /* The next character should define a new mode or
                       a delete operation */
                    ast_log(LOG_DEBUGG, "Selector - '%c'\n", *s);
                    switch (*s)
                    {
                    case '2':
                        s++;
                        /* Backspace */
                        if (t > entered_text)
                        {
                            t--;
                            u += sprintf(u, "delete ");
                            r = char_to_text(*t);
                            if (r)
                                u += sprintf(u, "%s, ", r);
                            else
                                u += sprintf(u, "%c, ", *t);
                            /*endif*/
                        }
                        /*endif*/
                        break;
                    case '5':
                        s++;
                        mode = TEXT_ENTRY_MODE_LOWER_CASE;
                        break;
                    case '6':
                        s++;
                        mode = TEXT_ENTRY_MODE_NUMERIC;
                        break;
                    case '7':
                        s++;
                        mode = TEXT_ENTRY_MODE_SYMBOL;
                        break;
                    case '8':
                        s++;
                        mode = TEXT_ENTRY_MODE_UPPER_CASE;
                        break;
                    case '9':
                        s++;
                        /* Backspace over word */
                        if (t > entered_text)
                        {
                            u += sprintf(u, "delete whole word, ");
                            t--;
                            while (t > entered_text  &&  *t == ' ')
                                t--;
                            /*endwhile*/
                            while (t > entered_text  &&  *t != ' ')
                                t--;
                            /*endwhile*/
                            if (*t == ' ')
                                t++;
                            /*endif*/
                        }
                        /*endif*/
                        break;
                    case '#':
                        s++;
                        /* Read back text to date, and continue entry */
                        u = talk_back;
                        *t = '\0';
                        u += sprintf(u, "%s", entered_text);
                        break;
                    }
                    /*endswitch*/
                    break;
                default:
                    /* Too many stars - treat this as a marker, like 1 star */
                    ast_log(LOG_DEBUGG, "Marker(like) - ignore\n");
                    break;
                }
                /*endswitch*/
            }
            else if (x == '#')
            {
                /* Terminate text entry */
                ast_log(LOG_DEBUGG, "Hash\n");
                *u = '\0';
                *t = '\0';
                done = 1;
            }
            else if (isdigit(x))
            {
                ast_log(LOG_DEBUGG, "Digit - %d of %c\n", hits, x);
                switch (mode)
                {
                case TEXT_ENTRY_MODE_LOWER_CASE:
                case TEXT_ENTRY_MODE_UPPER_CASE:
		    ast_log(LOG_DEBUGG, "Text entry\n");
		    q = uclc_presses[x - '0'];
                    q += ((hits - 1)%strlen(q));
                    if (mode == TEXT_ENTRY_MODE_LOWER_CASE)
                        *t = tolower(*q);
                    else
                        *t = *q;
                    /*endif*/
                    if (*t == ' ')
                    {
                        /* End of word? */
                        if (t > entered_text  &&  *(t - 1) != ' ')
                        {
                            u = ul;
                            v = t;
                            while (v > entered_text  &&  *v == ' ')
                                v--;
                            /*endwhile*/
                            while (v > entered_text  &&  *v != ' ')
                                v--;
                            /*endwhile*/
                            while (v <= t)
                                *u++ = *v++;
                            /*endwhile*/
                            ul = u;
                        }
                        else
                        {
                            u += sprintf(u, "space, ");
                        }
                        /*endif*/
                    }
                    else
                    {
                        r = char_to_text(*t);
                        if (r)
                            u += sprintf(u, "%s, ", r);
                        else
                            u += sprintf(u, "%c, ", *t);
                        /*endif*/
                    }
                    /*endif*/
                    break;
                case TEXT_ENTRY_MODE_NUMERIC:
		    ast_log(LOG_DEBUGG, "Numeric entry\n");
                    for (i = 1;  i < hits;  i++)
                    {
                        *t++ = x;
                        u += sprintf(u, "%c, ", x);
                    }
                    /*endfor*/
                    *t = x;
                    u += sprintf(u, "%c, ", x);
                    break;
                case TEXT_ENTRY_MODE_SYMBOL:
		    ast_log(LOG_DEBUGG, "Symbol entry\n");
                    q = symbol_presses[x - '0'];
                    q += ((hits - 1)%strlen(q));
                    if (mode == TEXT_ENTRY_MODE_LOWER_CASE)
                        *t = tolower(*q);
                    else
                        *t = *q;
                    /*endif*/
                    u += sprintf(u, "%c, ", *t);
                    break;
                }
                /*endif*/
                t++;
                if ((t - entered_text) >= max_chars)
                    done = 1;
                /*endif*/
            }
            else
            {
                /* Bad character! (perhaps an A-D). Ignore it */
            }
            /*endif*/
        }
        /*endwhile*/
        *u =
        *t = '\0';

        if (done  ||  total_timer <= 0)
        {
            res = 0;
            break;
        }
        /*endif*/

        ast_log(LOG_WARNING, "Text so far '%s'\n", entered_text);
        ast_log(LOG_WARNING, "Entered '%s'\n", talk_back);
        digval[0] = '\0';
        digits = 0;
        timer = PRE_DIGIT_TIMEOUT;
    }
    /*endwhile*/
    ast_log(LOG_WARNING, "Entered text: \"%s\"\n", entered_text);
    pbx_builtin_setvar_helper(chan, (char *) variable_name, entered_text);
    if (original_read_fmt.id != AST_FORMAT_SLINEAR)
    {
        res = ast_set_read_format_by_id(chan, original_read_fmt.id);
        if (res)
            ast_log(LOG_WARNING, "Unable to restore read format on '%s'\n", 
		    ast_channel_name(chan));
        /*endif*/
    }
    /*endif*/
    return  res;
}

static int dtmftotext_exec(struct ast_channel *chan, const char *data)
{
    char *variable_name;
    char *initial_digits;
    char *max_chars;
    char *max_time;
    char *stringp;
    int imax_chars;
    int imax_time;
    int res;
    
    res = 0;
    stringp = alloca(strlen(data) + 1);
    strncpy(stringp, data, strlen(data) + 1);
    if (strchr(stringp, '|')  &&  strchr(stringp, '='))
    {
        variable_name = strsep(&stringp, "=");
        initial_digits = strsep(&stringp, "|");
        max_chars = strsep(&stringp, "|");
        max_time = strsep(&stringp, "\0");
        if (variable_name == NULL  ||  initial_digits == NULL  ||  max_chars == NULL  ||  max_time == NULL)
        {
            ast_log(LOG_WARNING, "Ignoring, since there is no argument: variable, initial digits, max chars, or timeout\n");
        }
        else
        {
            imax_chars = atoi(max_chars);
            imax_time = atoi(max_time);
            if (variable_name  &&  initial_digits)
            {
	      if (ast_channel_state(chan) != AST_STATE_UP)
                {
                    /* Shouldn't need this, but checking to see if channel is already answered
                     * Theoretically asterisk should already have answered before running the app */
                    res = ast_answer(chan);
                }
                /*endif*/
                if (res == 0)
                    res = get_input_text(chan, variable_name, initial_digits, imax_chars, imax_time);
                /*endif*/
            }
            /*endif*/
        }
        /*endif*/
    }
    else
    {
        ast_log(LOG_WARNING, "Ignoring, no parameters\n");
    }
    /*endif*/
ast_log(LOG_WARNING, "Done!\n");
    return res;
}

static int unload_module(void)
{
      return ast_unregister_application(app);
}

static int load_module(void)
{
      return ast_register_application(app, dtmftotext_exec, synopsis, descrip);
}


AST_MODULE_INFO_STANDARD(ASTERISK_GPL_KEY, "DTMF To Text Application");

