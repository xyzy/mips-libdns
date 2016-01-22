
#line 1 "zone.rl"
/* ==========================================================================
 * zone.rl - RFC 1035 Master File Parser
 * --------------------------------------------------------------------------
 * Copyright (c) 2010  William Ahern
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to permit
 * persons to whom the Software is furnished to do so, subject to the
 * following conditions:
 *
 * The above copyright notice and this permission notice shall be included
 * in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
 * OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN
 * NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
 * DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR
 * OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE
 * USE OR OTHER DEALINGS IN THE SOFTWARE.
 * ==========================================================================
 */
#include <stddef.h>	/* NULL */
#include <stdlib.h>	/* malloc(3) free(3) */
#include <stdio.h>	/* fopen(3) fclose(3) fread(3) fputc(3) */

#include <string.h>	/* memset(3) memmove(3) */

#include <ctype.h>	/* isspace(3) isgraph(3) isdigit(3) */

#include <assert.h>	/* assert(3) */

#include <errno.h>	/* errno */

#include <arpa/inet.h>	/* inet_pton(3) */

#include "dns.h"
#include "zone.h"


#ifndef lengthof
#define lengthof(a) (sizeof (a) / sizeof (a)[0])
#endif

#ifndef endof
#define endof(a) (&(a)[lengthof(a)])
#endif

#ifndef MIN
#define MIN(a, b) (((a) < (b))? (a) : (b))
#endif


#define SAY_(fmt, ...) \
	do { fprintf(stderr, fmt "%.1s", __func__, __LINE__, __VA_ARGS__); } while (0)
#define SAY(...) SAY_(">>>> (%s:%d) " __VA_ARGS__, "\n")
#define HAI SAY("HAI")


#if __clang__
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wunused-variable"
#elif (__GNUC__ == 4 && __GNUC_MINOR__ >= 6) || __GNUC__ > 4
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-variable"
#endif


/*
 * P R E - P R O C E S S I N G  R O U T I N E S
 *
 * Outputs an encoded normal form of the RFC1035 master file syntax.
 *
 * o Linear spaces and tabs trimmed.
 *
 * o Multi-line groups are folded, with grouping parentheses replaced by
 *   spaces.
 *
 * o Comments are discarded.
 *
 * o Quoted and escaped whitespace characters are coded as a short with the
 *   T_LIT bit set.
 *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * */

#define T_LIT 0x0100

struct zonepp {
	int escaped, quoted, grouped, comment, lastc;
	struct { int v, n; } octet;
}; /* struct zonepp */

#define islwsp(ch) ((ch) == ' ' || (ch) == '\t')

static size_t fold(short *dst, size_t lim, unsigned char **src, size_t *len, struct zonepp *state) {
	short *p, *pe;
	int ch;

	if (!state->lastc)
		state->lastc = '\n';

	p  = dst;
	pe = p + lim;

	while (p < pe && *len) {
		ch = **src;

		if (state->escaped) {
			if (state->octet.n && (state->octet.n >= 3 || !isdigit(ch))) {
				state->escaped = 0;

				ch = state->octet.v;
				state->octet.v = 0;
				state->octet.n = 0;

				if (isspace(ch))
					ch |= T_LIT;

				*p++ = ch;

				continue; /* don't skip current char */
			} else if (isdigit(ch)) {
				state->octet.v *= 10;
				state->octet.v += ch - '0';
				state->octet.n++;

				goto skip;
			} else {
				state->escaped = 0;

				if (isspace(ch))
					ch |= T_LIT;

				goto copy;
			}
		} else if (state->comment) {
			if (ch != '\n')
				goto skip;

			state->comment = 0;
		}

test:
		switch (ch) {
		case '\\':
			state->escaped = 1;

			goto skip;
		case ';':
			if (state->quoted)
				break;

			state->comment = 1;

			goto skip;
		case '"':
			state->quoted = !state->quoted;

			goto skip;
		case '(':
			if (state->quoted || state->grouped)
				break;

			state->grouped = 1;

			ch = ' ';

			goto test;
		case ')':
			if (state->quoted || !state->grouped)
				break;

			state->grouped = 0;
			
			ch = ' ';

			goto test;
		case '\n':
			if (state->quoted) {
				break;
			} else if (state->lastc == '\n') {
				goto skip;
			} else if (state->grouped) {
				ch = ' ';

				goto test;
			}

			break;
		case '\t':
			ch = ' ';

			goto test;
		case ' ':
			if (state->quoted)
				break;
			else if (islwsp(state->lastc))
				goto skip;

			break;
		} /* switch() */
copy:
		if (state->quoted && isspace((0xff & ch)))
			ch |= T_LIT;

		state->lastc = *p = ch;

		++p;
skip:
		++*src;
		--*len;
	} /* while() */

	return p - dst;
} /* fold() */


struct tokens {
	short base[4096];
	unsigned count;
}; /* struct tokens */


static unsigned tok_eol(struct tokens *b) {
	unsigned i;

	for (i = 0; i < b->count; i++) {
		if (b->base[i] == '\n')
			return i + 1;
	}

	return 0;
} /* tok_eol() */


static void tok_discard(struct tokens *b, unsigned count) {
	if (count) {
		memmove(b->base, &b->base[count], 2 * (b->count - count));
		b->count = b->count - count;
	}
} /* tok_discard() */


struct zonefile {
	unsigned ttl;
	char origin[DNS_D_MAXNAME + 1];
	char lastrr[DNS_D_MAXNAME + 1];

	struct dns_soa soa;

	struct tokens toks;
	struct zonepp pp;
}; /* struct zonefile */


void zone_init(struct zonefile *P, const char *origin, unsigned ttl) {
	memset(P, 0, sizeof *P);

	origin = (origin)? origin : ".";
	dns_strlcpy(P->origin, origin, sizeof P->origin);
	dns_strlcpy(P->lastrr, origin, sizeof P->lastrr);

	P->ttl = (ttl)? ttl : 3600;
} /* zone_init() */


void zonerr_init(struct zonerr *rr, struct zonefile *P) {
	memset(rr, 0, sizeof *rr);
	rr->class = DNS_C_IN;
	rr->ttl   = P->ttl;
	dns_any_init(&rr->data, sizeof rr->data);
} /* zonerr_init() */



#line 433 "zone.rl"


struct zonerr *zone_getrr(struct zonerr *rr, struct dns_soa **soa, struct zonefile *P) {
	
#line 287 "zone.c"
static const char _file_grammar_actions[] = {
	0, 1, 0, 1, 2, 1, 5, 1, 
	10, 1, 12, 1, 15, 1, 16, 1, 
	17, 1, 18, 1, 19, 1, 20, 1, 
	22, 1, 23, 1, 25, 1, 27, 1, 
	28, 1, 29, 1, 30, 1, 34, 1, 
	35, 1, 36, 1, 37, 1, 39, 1, 
	41, 1, 43, 1, 44, 1, 46, 1, 
	47, 1, 49, 1, 51, 1, 52, 1, 
	54, 1, 55, 1, 57, 1, 58, 2, 
	1, 2, 2, 2, 5, 2, 2, 10, 
	2, 3, 14, 2, 3, 40, 2, 3, 
	42, 2, 4, 5, 2, 10, 6, 2, 
	10, 7, 2, 10, 8, 2, 10, 9, 
	2, 10, 16, 2, 10, 17, 2, 10, 
	18, 2, 10, 19, 2, 10, 55, 2, 
	10, 57, 2, 33, 32, 2, 34, 32, 
	2, 38, 32, 2, 45, 46, 2, 47, 
	48, 2, 57, 55, 3, 2, 10, 6, 
	3, 2, 10, 7, 3, 2, 10, 8, 
	3, 2, 10, 9, 3, 3, 11, 13, 
	3, 3, 11, 21, 3, 3, 11, 24, 
	3, 3, 11, 26, 3, 3, 11, 31, 
	3, 3, 11, 50, 3, 3, 11, 53, 
	3, 3, 11, 56, 3, 10, 57, 55, 
	3, 51, 4, 5, 3, 52, 4, 5, 
	3, 54, 4, 5, 4, 1, 2, 4, 
	5, 4, 3, 11, 56, 12, 4, 3, 
	11, 56, 20, 4, 3, 11, 56, 22, 
	4, 3, 11, 56, 25, 4, 3, 11, 
	56, 27, 4, 3, 11, 56, 35, 4, 
	3, 11, 56, 39, 4, 3, 11, 56, 
	41, 4, 3, 11, 56, 43, 4, 3, 
	11, 56, 44, 4, 3, 11, 56, 49, 
	4, 3, 11, 56, 55, 5, 3, 11, 
	56, 10, 55
};

static const short _file_grammar_key_offsets[] = {
	0, 0, 3, 21, 36, 56, 71, 88, 
	93, 98, 101, 103, 106, 108, 111, 113, 
	116, 117, 120, 121, 124, 125, 127, 129, 
	132, 142, 144, 146, 148, 150, 153, 156, 
	158, 161, 166, 171, 174, 176, 179, 182, 
	184, 186, 189, 192, 200, 202, 205, 208, 
	211, 214, 217, 222, 227, 232, 247, 252, 
	267, 272, 287, 292, 295, 298, 301, 303, 
	306, 309, 311, 314, 319, 324, 329, 334, 
	339, 344, 347, 349, 351, 353, 356, 361, 
	366, 371, 376, 385, 391, 393, 395, 398, 
	401, 402, 403, 419, 422, 427, 431, 435, 
	439, 443, 447, 450, 470, 474, 478, 481, 
	499, 502, 520, 525, 530, 533, 538, 541, 
	551, 554, 557, 560, 563, 578, 581, 584, 
	587, 596, 599, 619, 639, 642, 657, 677, 
	680, 685, 690, 695, 700, 703, 713, 718, 
	723, 728, 733, 736, 739, 743, 746, 765, 
	770, 773, 778, 783, 786, 789, 794, 799, 
	802, 805, 816, 821, 824, 827, 832, 835, 
	838, 843, 846, 851, 856, 861, 866, 869, 
	874, 879, 884, 887, 902, 922
};

static const short _file_grammar_trans_keys[] = {
	32, 9, 13, 32, 65, 67, 73, 77, 
	78, 80, 83, 84, 97, 99, 109, 110, 
	112, 115, 116, 48, 57, 32, 68, 72, 
	77, 83, 87, 100, 104, 109, 115, 119, 
	9, 13, 48, 57, 32, 65, 67, 73, 
	77, 78, 80, 83, 84, 97, 99, 109, 
	110, 112, 115, 116, 9, 13, 48, 57, 
	32, 68, 72, 77, 83, 87, 100, 104, 
	109, 115, 119, 9, 13, 48, 57, 32, 
	65, 67, 77, 78, 80, 83, 84, 97, 
	99, 109, 110, 112, 115, 116, 9, 13, 
	32, 65, 97, 9, 13, 32, 9, 13, 
	48, 57, 46, 48, 57, 48, 57, 46, 
	48, 57, 48, 57, 46, 48, 57, 48, 
	57, 46, 48, 57, 46, 46, 48, 57, 
	46, 46, 48, 57, 46, 65, 97, 65, 
	97, 32, 9, 13, 32, 46, 9, 13, 
	48, 58, 65, 70, 97, 102, 78, 110, 
	65, 97, 77, 109, 69, 101, 32, 9, 
	13, 32, 9, 13, 88, 120, 32, 9, 
	13, 32, 9, 13, 48, 57, 32, 9, 
	13, 48, 57, 32, 9, 13, 83, 115, 
	32, 9, 13, 32, 9, 13, 84, 116, 
	82, 114, 32, 9, 13, 32, 9, 13, 
	79, 80, 82, 83, 111, 112, 114, 115, 
	65, 97, 32, 9, 13, 32, 9, 13, 
	32, 9, 13, 32, 9, 13, 32, 9, 
	13, 32, 9, 13, 48, 57, 32, 9, 
	13, 48, 57, 32, 9, 13, 48, 57, 
	32, 68, 72, 77, 83, 87, 100, 104, 
	109, 115, 119, 9, 13, 48, 57, 32, 
	9, 13, 48, 57, 32, 68, 72, 77, 
	83, 87, 100, 104, 109, 115, 119, 9, 
	13, 48, 57, 32, 9, 13, 48, 57, 
	32, 68, 72, 77, 83, 87, 100, 104, 
	109, 115, 119, 9, 13, 48, 57, 32, 
	9, 13, 48, 57, 32, 9, 13, 32, 
	9, 13, 32, 9, 13, 70, 102, 32, 
	9, 13, 32, 9, 13, 86, 118, 32, 
	9, 13, 32, 9, 13, 48, 57, 32, 
	9, 13, 48, 57, 32, 9, 13, 48, 
	57, 32, 9, 13, 48, 57, 32, 9, 
	13, 48, 57, 32, 9, 13, 48, 57, 
	32, 9, 13, 72, 104, 70, 102, 80, 
	112, 32, 9, 13, 32, 9, 13, 48, 
	57, 32, 9, 13, 48, 57, 32, 9, 
	13, 48, 57, 32, 9, 13, 48, 57, 
	32, 9, 13, 48, 57, 65, 70, 97, 
	102, 48, 57, 65, 70, 97, 102, 88, 
	120, 84, 116, 32, 9, 13, 32, 9, 
	13, 78, 32, 65, 67, 77, 78, 80, 
	83, 84, 97, 99, 109, 110, 112, 115, 
	116, 48, 57, 32, 9, 13, 32, 79, 
	84, 9, 13, 32, 82, 9, 13, 32, 
	73, 9, 13, 32, 71, 9, 13, 32, 
	73, 9, 13, 32, 78, 9, 13, 32, 
	9, 13, 32, 65, 67, 73, 77, 78, 
	80, 83, 84, 97, 99, 109, 110, 112, 
	115, 116, 9, 13, 48, 57, 32, 84, 
	9, 13, 32, 76, 9, 13, 32, 9, 
	13, 32, 65, 67, 73, 77, 78, 80, 
	83, 84, 97, 99, 109, 110, 112, 115, 
	116, 48, 57, 32, 9, 13, 32, 65, 
	67, 73, 77, 78, 80, 83, 84, 97, 
	99, 109, 110, 112, 115, 116, 48, 57, 
	32, 36, 64, 9, 13, 32, 9, 13, 
	48, 57, 32, 9, 13, 32, 9, 13, 
	48, 57, 32, 9, 13, 32, 46, 9, 
	13, 48, 58, 65, 70, 97, 102, 32, 
	9, 13, 32, 9, 13, 32, 9, 13, 
	32, 9, 13, 32, 68, 72, 77, 83, 
	87, 100, 104, 109, 115, 119, 9, 13, 
	48, 57, 32, 9, 13, 32, 9, 13, 
	32, 9, 13, 32, 9, 13, 48, 57, 
	65, 70, 97, 102, 32, 9, 13, 32, 
	65, 67, 73, 77, 78, 80, 83, 84, 
	97, 99, 109, 110, 112, 115, 116, 9, 
	13, 48, 57, 32, 65, 67, 73, 77, 
	78, 80, 83, 84, 97, 99, 109, 110, 
	112, 115, 116, 9, 13, 48, 57, 32, 
	9, 13, 32, 68, 72, 77, 83, 87, 
	100, 104, 109, 115, 119, 9, 13, 48, 
	57, 32, 65, 67, 73, 77, 78, 80, 
	83, 84, 97, 99, 109, 110, 112, 115, 
	116, 9, 13, 48, 57, 32, 9, 13, 
	32, 65, 97, 9, 13, 32, 9, 13, 
	48, 57, 32, 65, 97, 9, 13, 32, 
	65, 97, 9, 13, 32, 9, 13, 32, 
	46, 9, 13, 48, 58, 65, 70, 97, 
	102, 32, 78, 110, 9, 13, 32, 65, 
	97, 9, 13, 32, 77, 109, 9, 13, 
	32, 69, 101, 9, 13, 32, 9, 13, 
	32, 9, 13, 32, 78, 9, 13, 32, 
	9, 13, 32, 65, 67, 77, 78, 80, 
	83, 84, 97, 99, 109, 110, 112, 115, 
	116, 9, 13, 48, 57, 32, 88, 120, 
	9, 13, 32, 9, 13, 32, 9, 13, 
	48, 57, 32, 83, 115, 9, 13, 32, 
	9, 13, 32, 9, 13, 32, 84, 116, 
	9, 13, 32, 82, 114, 9, 13, 32, 
	9, 13, 32, 9, 13, 32, 79, 80, 
	82, 83, 111, 112, 114, 115, 9, 13, 
	32, 65, 97, 9, 13, 32, 9, 13, 
	32, 9, 13, 32, 70, 102, 9, 13, 
	32, 9, 13, 32, 9, 13, 32, 86, 
	118, 9, 13, 32, 9, 13, 32, 9, 
	13, 48, 57, 32, 72, 104, 9, 13, 
	32, 70, 102, 9, 13, 32, 80, 112, 
	9, 13, 32, 9, 13, 32, 9, 13, 
	48, 57, 32, 88, 120, 9, 13, 32, 
	84, 116, 9, 13, 32, 9, 13, 32, 
	68, 72, 77, 83, 87, 100, 104, 109, 
	115, 119, 9, 13, 48, 57, 32, 65, 
	67, 73, 77, 78, 80, 83, 84, 97, 
	99, 109, 110, 112, 115, 116, 9, 13, 
	48, 57, 32, 9, 13, 0
};

static const char _file_grammar_single_lengths[] = {
	0, 1, 16, 11, 16, 11, 15, 3, 
	1, 1, 0, 1, 0, 1, 0, 1, 
	1, 1, 1, 1, 1, 2, 2, 1, 
	2, 2, 2, 2, 2, 1, 1, 2, 
	1, 1, 1, 1, 2, 1, 1, 2, 
	2, 1, 1, 8, 2, 1, 1, 1, 
	1, 1, 1, 1, 1, 11, 1, 11, 
	1, 11, 1, 1, 1, 1, 2, 1, 
	1, 2, 1, 1, 1, 1, 1, 1, 
	1, 1, 2, 2, 2, 1, 1, 1, 
	1, 1, 1, 0, 2, 2, 1, 1, 
	1, 1, 14, 1, 3, 2, 2, 2, 
	2, 2, 1, 16, 2, 2, 1, 16, 
	1, 16, 3, 1, 1, 1, 1, 2, 
	1, 1, 1, 1, 11, 1, 1, 1, 
	1, 1, 16, 16, 1, 11, 16, 1, 
	3, 1, 3, 3, 1, 2, 3, 3, 
	3, 3, 1, 1, 2, 1, 15, 3, 
	1, 1, 3, 1, 1, 3, 3, 1, 
	1, 9, 3, 1, 1, 3, 1, 1, 
	3, 1, 1, 3, 3, 3, 1, 1, 
	3, 3, 1, 11, 16, 1
};

static const char _file_grammar_range_lengths[] = {
	0, 1, 1, 2, 2, 2, 1, 1, 
	2, 1, 1, 1, 1, 1, 1, 1, 
	0, 1, 0, 1, 0, 0, 0, 1, 
	4, 0, 0, 0, 0, 1, 1, 0, 
	1, 2, 2, 1, 0, 1, 1, 0, 
	0, 1, 1, 0, 0, 1, 1, 1, 
	1, 1, 2, 2, 2, 2, 2, 2, 
	2, 2, 2, 1, 1, 1, 0, 1, 
	1, 0, 1, 2, 2, 2, 2, 2, 
	2, 1, 0, 0, 0, 1, 2, 2, 
	2, 2, 4, 3, 0, 0, 1, 1, 
	0, 0, 1, 1, 1, 1, 1, 1, 
	1, 1, 1, 2, 1, 1, 1, 1, 
	1, 1, 1, 2, 1, 2, 1, 4, 
	1, 1, 1, 1, 2, 1, 1, 1, 
	4, 1, 2, 2, 1, 2, 2, 1, 
	1, 2, 1, 1, 1, 4, 1, 1, 
	1, 1, 1, 1, 1, 1, 2, 1, 
	1, 2, 1, 1, 1, 1, 1, 1, 
	1, 1, 1, 1, 1, 1, 1, 1, 
	1, 1, 2, 1, 1, 1, 1, 2, 
	1, 1, 1, 2, 2, 1
};

static const short _file_grammar_index_offsets[] = {
	0, 0, 3, 21, 35, 54, 68, 85, 
	90, 94, 97, 99, 102, 104, 107, 109, 
	112, 114, 117, 119, 122, 124, 127, 130, 
	133, 140, 143, 146, 149, 152, 155, 158, 
	161, 164, 168, 172, 175, 178, 181, 184, 
	187, 190, 193, 196, 205, 208, 211, 214, 
	217, 220, 223, 227, 231, 235, 249, 253, 
	267, 271, 285, 289, 292, 295, 298, 301, 
	304, 307, 310, 313, 317, 321, 325, 329, 
	333, 337, 340, 343, 346, 349, 352, 356, 
	360, 364, 368, 374, 378, 381, 384, 387, 
	390, 392, 394, 410, 413, 418, 422, 426, 
	430, 434, 438, 441, 460, 464, 468, 471, 
	489, 492, 510, 515, 519, 522, 526, 529, 
	536, 539, 542, 545, 548, 562, 565, 568, 
	571, 577, 580, 599, 618, 621, 635, 654, 
	657, 662, 666, 671, 676, 679, 686, 691, 
	696, 701, 706, 709, 712, 716, 719, 737, 
	742, 745, 749, 754, 757, 760, 765, 770, 
	773, 776, 787, 792, 795, 798, 803, 806, 
	809, 814, 817, 821, 826, 831, 836, 839, 
	843, 848, 853, 856, 870, 889
};

static const unsigned char _file_grammar_trans_targs[] = {
	2, 0, 1, 2, 7, 25, 88, 31, 
	36, 39, 43, 84, 7, 25, 31, 36, 
	39, 43, 84, 3, 0, 4, 91, 91, 
	91, 91, 91, 91, 91, 91, 91, 91, 
	4, 3, 0, 4, 7, 25, 88, 31, 
	36, 39, 43, 84, 7, 25, 31, 36, 
	39, 43, 84, 4, 5, 0, 6, 87, 
	87, 87, 87, 87, 87, 87, 87, 87, 
	87, 6, 5, 0, 6, 7, 25, 31, 
	36, 39, 43, 84, 7, 25, 31, 36, 
	39, 43, 84, 6, 0, 8, 21, 21, 
	8, 0, 8, 8, 9, 0, 10, 19, 
	0, 11, 0, 12, 17, 0, 13, 0, 
	14, 15, 0, 107, 0, 14, 16, 0, 
	14, 0, 12, 18, 0, 12, 0, 10, 
	20, 0, 10, 0, 22, 22, 0, 23, 
	23, 0, 24, 24, 0, 24, 111, 24, 
	111, 111, 111, 0, 26, 26, 0, 27, 
	27, 0, 28, 28, 0, 29, 29, 0, 
	30, 30, 0, 30, 30, 112, 32, 32, 
	0, 33, 33, 0, 33, 33, 34, 0, 
	35, 35, 34, 0, 35, 35, 113, 37, 
	37, 0, 38, 38, 0, 38, 38, 114, 
	40, 40, 0, 41, 41, 0, 42, 42, 
	0, 42, 42, 115, 44, 62, 65, 74, 
	44, 62, 65, 74, 0, 45, 45, 0, 
	46, 46, 0, 46, 46, 47, 48, 48, 
	47, 48, 48, 49, 50, 50, 49, 50, 
	50, 51, 0, 52, 52, 51, 0, 52, 
	52, 53, 0, 54, 61, 61, 61, 61, 
	61, 61, 61, 61, 61, 61, 54, 53, 
	0, 54, 54, 55, 0, 56, 60, 60, 
	60, 60, 60, 60, 60, 60, 60, 60, 
	56, 55, 0, 56, 56, 57, 0, 58, 
	59, 59, 59, 59, 59, 59, 59, 59, 
	59, 59, 58, 57, 0, 58, 58, 116, 
	0, 58, 58, 0, 56, 56, 0, 54, 
	54, 0, 63, 63, 0, 64, 64, 0, 
	64, 64, 118, 66, 66, 0, 67, 67, 
	0, 67, 67, 68, 0, 69, 69, 68, 
	0, 69, 69, 70, 0, 71, 71, 70, 
	0, 71, 71, 72, 0, 73, 73, 72, 
	0, 73, 73, 119, 75, 75, 0, 76, 
	76, 0, 77, 77, 0, 78, 78, 0, 
	78, 78, 79, 0, 80, 80, 79, 0, 
	80, 80, 81, 0, 82, 82, 81, 0, 
	82, 82, 83, 83, 83, 0, 120, 120, 
	120, 0, 85, 85, 0, 86, 86, 0, 
	64, 64, 0, 6, 6, 0, 89, 0, 
	90, 0, 7, 25, 31, 36, 39, 43, 
	84, 7, 25, 31, 36, 39, 43, 84, 
	5, 0, 4, 4, 0, 2, 93, 100, 
	0, 1, 2, 94, 0, 1, 2, 95, 
	0, 1, 2, 96, 0, 1, 2, 97, 
	0, 1, 2, 98, 0, 1, 99, 0, 
	1, 2, 128, 134, 140, 143, 146, 149, 
	153, 168, 128, 134, 143, 146, 149, 153, 
	168, 0, 125, 124, 2, 101, 0, 1, 
	2, 102, 0, 1, 103, 0, 1, 2, 
	7, 25, 88, 31, 36, 39, 43, 84, 
	7, 25, 31, 36, 39, 43, 84, 171, 
	0, 105, 0, 1, 2, 7, 25, 88, 
	31, 36, 39, 43, 84, 7, 25, 31, 
	36, 39, 43, 84, 3, 0, 122, 92, 
	104, 121, 1, 108, 108, 109, 0, 108, 
	108, 0, 108, 108, 110, 0, 108, 108, 
	0, 108, 111, 108, 111, 111, 111, 0, 
	108, 108, 112, 108, 108, 113, 108, 108, 
	114, 108, 108, 115, 117, 117, 117, 117, 
	117, 117, 117, 117, 117, 117, 117, 117, 
	116, 0, 117, 117, 0, 108, 108, 118, 
	108, 108, 119, 108, 108, 83, 83, 83, 
	0, 121, 121, 0, 123, 7, 25, 88, 
	31, 36, 39, 43, 84, 7, 25, 31, 
	36, 39, 43, 84, 121, 3, 0, 123, 
	7, 25, 88, 31, 36, 39, 43, 84, 
	7, 25, 31, 36, 39, 43, 84, 121, 
	3, 0, 108, 108, 124, 126, 127, 127, 
	127, 127, 127, 127, 127, 127, 127, 127, 
	126, 125, 124, 126, 7, 25, 88, 31, 
	36, 39, 43, 84, 7, 25, 31, 36, 
	39, 43, 84, 126, 5, 0, 126, 126, 
	124, 129, 130, 130, 129, 124, 129, 129, 
	9, 0, 108, 131, 131, 108, 124, 108, 
	132, 132, 108, 124, 133, 133, 124, 133, 
	111, 133, 111, 111, 111, 0, 108, 135, 
	135, 108, 124, 108, 136, 136, 108, 124, 
	108, 137, 137, 108, 124, 108, 138, 138, 
	108, 124, 139, 139, 124, 139, 139, 112, 
	108, 141, 108, 124, 142, 108, 124, 108, 
	7, 25, 31, 36, 39, 43, 84, 7, 
	25, 31, 36, 39, 43, 84, 108, 5, 
	0, 108, 144, 144, 108, 124, 145, 145, 
	124, 145, 145, 34, 0, 108, 147, 147, 
	108, 124, 148, 148, 124, 148, 148, 114, 
	108, 150, 150, 108, 124, 108, 151, 151, 
	108, 124, 152, 152, 124, 152, 152, 115, 
	108, 154, 157, 160, 163, 154, 157, 160, 
	163, 108, 124, 108, 155, 155, 108, 124, 
	156, 156, 124, 156, 156, 47, 108, 158, 
	158, 108, 124, 159, 159, 124, 159, 159, 
	118, 108, 161, 161, 108, 124, 162, 162, 
	124, 162, 162, 68, 0, 108, 164, 164, 
	108, 124, 108, 165, 165, 108, 124, 108, 
	166, 166, 108, 124, 167, 167, 124, 167, 
	167, 79, 0, 108, 169, 169, 108, 124, 
	108, 170, 170, 108, 124, 159, 159, 124, 
	172, 173, 173, 173, 173, 173, 173, 173, 
	173, 173, 173, 172, 171, 0, 172, 7, 
	25, 88, 31, 36, 39, 43, 84, 7, 
	25, 31, 36, 39, 43, 84, 172, 5, 
	0, 172, 172, 0, 0
};

static const short _file_grammar_trans_actions[] = {
	180, 1, 3, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 89, 1, 116, 95, 98, 
	101, 7, 92, 95, 98, 101, 7, 92, 
	116, 5, 1, 65, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 65, 89, 1, 116, 95, 
	98, 101, 7, 92, 95, 98, 101, 7, 
	92, 116, 5, 1, 65, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 65, 1, 51, 0, 0, 
	51, 1, 0, 0, 131, 1, 55, 53, 
	1, 131, 1, 55, 53, 1, 131, 1, 
	55, 53, 1, 131, 1, 55, 53, 1, 
	55, 1, 55, 53, 1, 55, 1, 55, 
	53, 1, 55, 1, 0, 0, 1, 0, 
	0, 1, 49, 49, 1, 0, 71, 0, 
	71, 71, 71, 1, 0, 0, 1, 0, 
	0, 1, 0, 0, 1, 0, 0, 1, 
	27, 27, 1, 0, 0, 71, 0, 0, 
	1, 23, 23, 1, 0, 0, 89, 1, 
	25, 25, 5, 1, 0, 0, 71, 0, 
	0, 1, 21, 21, 1, 0, 0, 71, 
	0, 0, 1, 0, 0, 1, 57, 57, 
	1, 0, 0, 71, 0, 0, 0, 0, 
	0, 0, 0, 0, 1, 0, 0, 1, 
	9, 9, 1, 0, 0, 71, 156, 156, 
	3, 0, 0, 71, 80, 80, 3, 0, 
	0, 89, 1, 11, 11, 5, 1, 0, 
	0, 89, 1, 104, 95, 98, 101, 7, 
	92, 95, 98, 101, 7, 92, 104, 5, 
	1, 13, 13, 89, 1, 107, 95, 98, 
	101, 7, 92, 95, 98, 101, 7, 92, 
	107, 5, 1, 15, 15, 89, 1, 110, 
	95, 98, 101, 7, 92, 95, 98, 101, 
	7, 92, 110, 5, 1, 17, 17, 89, 
	1, 17, 17, 1, 15, 15, 1, 13, 
	13, 1, 0, 0, 1, 47, 47, 1, 
	0, 0, 71, 0, 0, 1, 29, 29, 
	1, 0, 0, 89, 1, 31, 31, 5, 
	1, 0, 0, 89, 1, 33, 33, 5, 
	1, 0, 0, 89, 1, 35, 35, 5, 
	1, 0, 0, 71, 0, 0, 1, 0, 
	0, 1, 0, 0, 1, 39, 39, 1, 
	0, 0, 89, 1, 41, 41, 5, 1, 
	0, 0, 89, 1, 43, 43, 5, 1, 
	0, 0, 128, 128, 128, 1, 122, 122, 
	122, 1, 0, 0, 1, 0, 0, 1, 
	45, 45, 1, 65, 65, 1, 0, 1, 
	0, 1, 63, 63, 63, 63, 63, 63, 
	63, 63, 63, 63, 63, 63, 63, 63, 
	200, 1, 65, 65, 1, 180, 3, 3, 
	1, 3, 180, 3, 1, 3, 180, 3, 
	1, 3, 180, 3, 1, 3, 180, 3, 
	1, 3, 180, 3, 1, 3, 180, 1, 
	3, 0, 71, 71, 71, 71, 71, 71, 
	71, 71, 71, 71, 71, 71, 71, 71, 
	71, 1, 204, 71, 180, 3, 1, 3, 
	180, 3, 1, 3, 180, 1, 3, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 89, 
	1, 180, 1, 3, 61, 61, 61, 61, 
	61, 61, 61, 61, 61, 61, 61, 61, 
	61, 61, 61, 61, 196, 1, 0, 71, 
	71, 0, 71, 134, 134, 53, 1, 0, 
	0, 1, 134, 134, 53, 1, 134, 134, 
	1, 86, 3, 86, 3, 3, 3, 1, 
	168, 168, 3, 164, 164, 3, 160, 160, 
	3, 176, 176, 3, 113, 95, 98, 101, 
	7, 92, 95, 98, 101, 7, 92, 113, 
	5, 1, 19, 19, 1, 83, 83, 3, 
	172, 172, 3, 37, 37, 125, 125, 125, 
	1, 0, 0, 1, 59, 59, 59, 59, 
	59, 59, 59, 59, 59, 59, 59, 59, 
	59, 59, 59, 59, 0, 192, 1, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	89, 1, 184, 184, 3, 269, 144, 148, 
	152, 77, 140, 144, 148, 152, 77, 140, 
	269, 74, 3, 65, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 65, 89, 1, 264, 264, 
	3, 254, 3, 3, 254, 3, 0, 0, 
	131, 1, 184, 3, 3, 184, 3, 184, 
	3, 3, 184, 3, 249, 249, 3, 0, 
	71, 0, 71, 71, 71, 1, 184, 3, 
	3, 184, 3, 184, 3, 3, 184, 3, 
	184, 3, 3, 184, 3, 184, 3, 3, 
	184, 3, 224, 224, 3, 0, 0, 71, 
	184, 3, 184, 3, 184, 184, 3, 0, 
	63, 63, 63, 63, 63, 63, 63, 63, 
	63, 63, 63, 63, 63, 63, 0, 200, 
	1, 184, 3, 3, 184, 3, 219, 219, 
	3, 0, 0, 89, 1, 184, 3, 3, 
	184, 3, 214, 214, 3, 0, 0, 71, 
	184, 3, 3, 184, 3, 184, 3, 3, 
	184, 3, 259, 259, 3, 0, 0, 71, 
	184, 3, 3, 3, 3, 3, 3, 3, 
	3, 184, 3, 184, 3, 3, 184, 3, 
	209, 209, 3, 0, 0, 71, 184, 3, 
	3, 184, 3, 244, 244, 3, 0, 0, 
	71, 184, 3, 3, 184, 3, 229, 229, 
	3, 0, 0, 89, 1, 184, 3, 3, 
	184, 3, 184, 3, 3, 184, 3, 184, 
	3, 3, 184, 3, 234, 234, 3, 0, 
	0, 89, 1, 184, 3, 3, 184, 3, 
	184, 3, 3, 184, 3, 239, 239, 3, 
	188, 95, 98, 101, 7, 92, 95, 98, 
	101, 7, 92, 188, 5, 1, 137, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 137, 89, 
	1, 137, 137, 1, 0
};

static const short _file_grammar_eof_actions[] = {
	0, 1, 1, 1, 1, 1, 1, 1, 
	1, 1, 1, 1, 1, 1, 1, 1, 
	1, 1, 1, 1, 1, 1, 1, 1, 
	1, 1, 1, 1, 1, 1, 1, 1, 
	1, 1, 1, 1, 1, 1, 1, 1, 
	1, 1, 1, 1, 1, 1, 1, 1, 
	1, 1, 1, 1, 1, 1, 1, 1, 
	1, 1, 1, 1, 1, 1, 1, 1, 
	1, 1, 1, 1, 1, 1, 1, 1, 
	1, 1, 1, 1, 1, 1, 1, 1, 
	1, 1, 1, 1, 1, 1, 1, 1, 
	1, 1, 1, 1, 1, 1, 1, 1, 
	1, 1, 1, 1, 1, 1, 1, 1, 
	1, 1, 69, 134, 0, 134, 134, 86, 
	168, 164, 160, 176, 113, 19, 83, 172, 
	37, 69, 69, 69, 184, 184, 0, 184, 
	184, 0, 184, 184, 184, 0, 184, 184, 
	184, 184, 184, 0, 184, 184, 0, 184, 
	184, 0, 184, 184, 0, 184, 184, 184, 
	0, 184, 184, 184, 0, 184, 184, 0, 
	184, 184, 0, 184, 184, 184, 184, 0, 
	184, 184, 184, 119, 67, 67
};

static const int file_grammar_start = 106;
static const int file_grammar_first_final = 106;
static const int file_grammar_error = 0;

static const int file_grammar_en_main = 106;


#line 437 "zone.rl"
	short *p, *pe, *eof;
	int cs;
	char str[1024], *sp, lc;
	unsigned span, ttl, n, i;

	span = 0;
next:
	tok_discard(&P->toks, span);

	if (!(span = tok_eol(&P->toks)))
		return NULL;

	sp  = str;
	lc  = 0;
	ttl = 0;
	n   = 0;
	i   = 0;

	zonerr_init(rr, P);

	
#line 829 "zone.c"
	{
	cs = file_grammar_start;
	}

#line 458 "zone.rl"

	p   = P->toks.base;
	pe  = p + span;
	eof = pe;

	
#line 841 "zone.c"
	{
	int _klen;
	unsigned int _trans;
	const char *_acts;
	unsigned int _nacts;
	const short *_keys;

	if ( p == pe )
		goto _test_eof;
	if ( cs == 0 )
		goto _out;
_resume:
	_keys = _file_grammar_trans_keys + _file_grammar_key_offsets[cs];
	_trans = _file_grammar_index_offsets[cs];

	_klen = _file_grammar_single_lengths[cs];
	if ( _klen > 0 ) {
		const short *_lower = _keys;
		const short *_mid;
		const short *_upper = _keys + _klen - 1;
		while (1) {
			if ( _upper < _lower )
				break;

			_mid = _lower + ((_upper-_lower) >> 1);
			if ( (*p) < *_mid )
				_upper = _mid - 1;
			else if ( (*p) > *_mid )
				_lower = _mid + 1;
			else {
				_trans += (unsigned int)(_mid - _keys);
				goto _match;
			}
		}
		_keys += _klen;
		_trans += _klen;
	}

	_klen = _file_grammar_range_lengths[cs];
	if ( _klen > 0 ) {
		const short *_lower = _keys;
		const short *_mid;
		const short *_upper = _keys + (_klen<<1) - 2;
		while (1) {
			if ( _upper < _lower )
				break;

			_mid = _lower + (((_upper-_lower) >> 1) & ~1);
			if ( (*p) < _mid[0] )
				_upper = _mid - 2;
			else if ( (*p) > _mid[1] )
				_lower = _mid + 2;
			else {
				_trans += (unsigned int)((_mid - _keys)>>1);
				goto _match;
			}
		}
		_trans += _klen;
	}

_match:
	cs = _file_grammar_trans_targs[_trans];

	if ( _file_grammar_trans_actions[_trans] == 0 )
		goto _again;

	_acts = _file_grammar_actions + _file_grammar_trans_actions[_trans];
	_nacts = (unsigned int) *_acts++;
	while ( _nacts-- > 0 )
	{
		switch ( *_acts++ )
		{
	case 0:
#line 282 "zone.rl"
	{
		fprintf(stderr, "OOPS: ");
		do {
			unsigned i, at = p - P->toks.base;
			for (i = 0; i < span; i++) {
				if (i == at) fputc('[', stderr);
				fputc((0xff & P->toks.base[i]), stderr);
				if (i == at) fputc(']', stderr);
			}
		} while(0);
		fputc('\n', stderr);
		goto next;
	}
	break;
	case 1:
#line 296 "zone.rl"
	{ sp = str; }
	break;
	case 2:
#line 297 "zone.rl"
	{ if (sp < endof(str)) *sp++ = (*p); lc = (*p); }
	break;
	case 3:
#line 298 "zone.rl"
	{ if (sp >= endof(str)) sp--; *sp = '\0'; }
	break;
	case 4:
#line 302 "zone.rl"
	{ n = 0; }
	break;
	case 5:
#line 302 "zone.rl"
	{ n *= 10; n += (*p) - '0'; }
	break;
	case 6:
#line 305 "zone.rl"
	{ ttl *= 604800; }
	break;
	case 7:
#line 306 "zone.rl"
	{ ttl *= 86400; }
	break;
	case 8:
#line 307 "zone.rl"
	{ ttl *= 3600; }
	break;
	case 9:
#line 308 "zone.rl"
	{ ttl *= 60; }
	break;
	case 10:
#line 310 "zone.rl"
	{ ttl = n; }
	break;
	case 11:
#line 312 "zone.rl"
	{
		 if (lc != '.') {
			if (P->origin[0] != '.')
				dns_strlcat(str, ".", sizeof str);
			dns_strlcat(str, P->origin, sizeof str); 
		}
	}
	break;
	case 12:
#line 322 "zone.rl"
	{ rr->type = DNS_T_SOA; }
	break;
	case 13:
#line 323 "zone.rl"
	{ dns_strlcpy(rr->data.soa.mname, str, sizeof rr->data.soa.mname); }
	break;
	case 14:
#line 324 "zone.rl"
	{ dns_strlcpy(rr->data.soa.rname, str, sizeof rr->data.soa.rname); }
	break;
	case 15:
#line 325 "zone.rl"
	{ rr->data.soa.serial = n; }
	break;
	case 16:
#line 326 "zone.rl"
	{ rr->data.soa.refresh = ttl; }
	break;
	case 17:
#line 327 "zone.rl"
	{ rr->data.soa.retry = ttl; }
	break;
	case 18:
#line 328 "zone.rl"
	{ rr->data.soa.expire = ttl; }
	break;
	case 19:
#line 329 "zone.rl"
	{ rr->data.soa.minimum = ttl; }
	break;
	case 20:
#line 332 "zone.rl"
	{ rr->type = DNS_T_NS; }
	break;
	case 21:
#line 333 "zone.rl"
	{ dns_strlcpy(rr->data.ns.host, str, sizeof rr->data.ns.host); }
	break;
	case 22:
#line 336 "zone.rl"
	{ rr->type = DNS_T_MX; }
	break;
	case 23:
#line 337 "zone.rl"
	{ rr->data.mx.preference = n; }
	break;
	case 24:
#line 338 "zone.rl"
	{ dns_strlcpy(rr->data.mx.host, str, sizeof rr->data.mx.host); }
	break;
	case 25:
#line 341 "zone.rl"
	{ rr->type = DNS_T_CNAME; }
	break;
	case 26:
#line 342 "zone.rl"
	{ dns_strlcpy(rr->data.cname.host, str, sizeof rr->data.cname.host); }
	break;
	case 27:
#line 345 "zone.rl"
	{ rr->type = DNS_T_SRV; }
	break;
	case 28:
#line 346 "zone.rl"
	{ rr->data.srv.priority = n; }
	break;
	case 29:
#line 347 "zone.rl"
	{ rr->data.srv.weight = n; }
	break;
	case 30:
#line 348 "zone.rl"
	{ rr->data.srv.port = n; }
	break;
	case 31:
#line 349 "zone.rl"
	{ dns_strlcpy(rr->data.srv.target, str, sizeof rr->data.srv.target); }
	break;
	case 32:
#line 352 "zone.rl"
	{
		if ((*p) >= '0' && (*p) <= '9') {
			n = (0x0f & ((*p) - '0'));
		} else if ((*p) >= 'A' && (*p) <= 'F') {
			n = (0x0f & (10 + ((*p) - 'A')));
		} else if ((*p) >= 'a' && (*p) <= 'f') {
			n = (0x0f & (10 + ((*p) - 'a')));
		}
	}
	break;
	case 33:
#line 364 "zone.rl"
	{
		if (i < sizeof rr->data.sshfp.digest)
			((unsigned char *)&rr->data.sshfp.digest)[i] = (0xf0 & (n << 4));
	}
	break;
	case 34:
#line 369 "zone.rl"
	{
		if (i < sizeof rr->data.sshfp.digest)
			((unsigned char *)&rr->data.sshfp.digest)[i] |= (0x0f & n);
		i++;
	}
	break;
	case 35:
#line 377 "zone.rl"
	{ rr->type = DNS_T_SSHFP; }
	break;
	case 36:
#line 378 "zone.rl"
	{ rr->data.sshfp.algo = n; }
	break;
	case 37:
#line 379 "zone.rl"
	{ rr->data.sshfp.type = n; }
	break;
	case 38:
#line 380 "zone.rl"
	{ i = 0; memset(&rr->data.sshfp.digest, 0, sizeof rr->data.sshfp.digest); }
	break;
	case 39:
#line 384 "zone.rl"
	{ rr->type = DNS_T_TXT; }
	break;
	case 40:
#line 385 "zone.rl"
	{ rr->data.txt.len = MIN(rr->data.txt.size - 1, sp - str); memcpy(rr->data.txt.data, str, rr->data.txt.len); }
	break;
	case 41:
#line 388 "zone.rl"
	{ rr->type = DNS_T_SPF; }
	break;
	case 42:
#line 391 "zone.rl"
	{
		if (1 != inet_pton(AF_INET6, str, &rr->data.aaaa.addr)) {
			SAY("invalid AAAA address: %s", str);
			goto next;
		}
	}
	break;
	case 43:
#line 398 "zone.rl"
	{ rr->type = DNS_T_AAAA; }
	break;
	case 44:
#line 403 "zone.rl"
	{ rr->type = DNS_T_A; }
	break;
	case 45:
#line 404 "zone.rl"
	{ n = 0; }
	break;
	case 46:
#line 404 "zone.rl"
	{ n *= 10; n += (*p) - '0'; }
	break;
	case 47:
#line 404 "zone.rl"
	{ rr->data.a.addr.s_addr <<= 8; rr->data.a.addr.s_addr |= (0xff & n); }
	break;
	case 48:
#line 405 "zone.rl"
	{ rr->data.a.addr.s_addr = htonl(rr->data.a.addr.s_addr); }
	break;
	case 49:
#line 408 "zone.rl"
	{ rr->type = DNS_T_PTR; }
	break;
	case 50:
#line 409 "zone.rl"
	{ dns_strlcpy(rr->data.ptr.host, str, sizeof rr->data.ptr.host); }
	break;
	case 51:
#line 414 "zone.rl"
	{ dns_strlcpy(rr->name, P->lastrr, sizeof rr->name); }
	break;
	case 52:
#line 415 "zone.rl"
	{ dns_strlcpy(rr->name, P->origin, sizeof rr->name); }
	break;
	case 53:
#line 416 "zone.rl"
	{ if (!rr->name[0]) dns_strlcpy(rr->name, str, sizeof rr->name); }
	break;
	case 54:
#line 420 "zone.rl"
	{ rr->class = DNS_C_IN; }
	break;
	case 55:
#line 422 "zone.rl"
	{ rr->ttl = ttl; }
	break;
	case 56:
#line 426 "zone.rl"
	{ dns_strlcpy(P->origin, str, sizeof P->origin); goto next; }
	break;
	case 57:
#line 428 "zone.rl"
	{ P->ttl = ttl; goto next; }
	break;
#line 1184 "zone.c"
		}
	}

_again:
	if ( cs == 0 )
		goto _out;
	if ( ++p != pe )
		goto _resume;
	_test_eof: {}
	if ( p == eof )
	{
	const char *__acts = _file_grammar_actions + _file_grammar_eof_actions[cs];
	unsigned int __nacts = (unsigned int) *__acts++;
	while ( __nacts-- > 0 ) {
		switch ( *__acts++ ) {
	case 0:
#line 282 "zone.rl"
	{
		fprintf(stderr, "OOPS: ");
		do {
			unsigned i, at = p - P->toks.base;
			for (i = 0; i < span; i++) {
				if (i == at) fputc('[', stderr);
				fputc((0xff & P->toks.base[i]), stderr);
				if (i == at) fputc(']', stderr);
			}
		} while(0);
		fputc('\n', stderr);
		goto next;
	}
	break;
	case 3:
#line 298 "zone.rl"
	{ if (sp >= endof(str)) sp--; *sp = '\0'; }
	break;
	case 10:
#line 310 "zone.rl"
	{ ttl = n; }
	break;
	case 11:
#line 312 "zone.rl"
	{
		 if (lc != '.') {
			if (P->origin[0] != '.')
				dns_strlcat(str, ".", sizeof str);
			dns_strlcat(str, P->origin, sizeof str); 
		}
	}
	break;
	case 19:
#line 329 "zone.rl"
	{ rr->data.soa.minimum = ttl; }
	break;
	case 21:
#line 333 "zone.rl"
	{ dns_strlcpy(rr->data.ns.host, str, sizeof rr->data.ns.host); }
	break;
	case 24:
#line 338 "zone.rl"
	{ dns_strlcpy(rr->data.mx.host, str, sizeof rr->data.mx.host); }
	break;
	case 26:
#line 342 "zone.rl"
	{ dns_strlcpy(rr->data.cname.host, str, sizeof rr->data.cname.host); }
	break;
	case 31:
#line 349 "zone.rl"
	{ dns_strlcpy(rr->data.srv.target, str, sizeof rr->data.srv.target); }
	break;
	case 34:
#line 369 "zone.rl"
	{
		if (i < sizeof rr->data.sshfp.digest)
			((unsigned char *)&rr->data.sshfp.digest)[i] |= (0x0f & n);
		i++;
	}
	break;
	case 40:
#line 385 "zone.rl"
	{ rr->data.txt.len = MIN(rr->data.txt.size - 1, sp - str); memcpy(rr->data.txt.data, str, rr->data.txt.len); }
	break;
	case 42:
#line 391 "zone.rl"
	{
		if (1 != inet_pton(AF_INET6, str, &rr->data.aaaa.addr)) {
			SAY("invalid AAAA address: %s", str);
			goto next;
		}
	}
	break;
	case 47:
#line 404 "zone.rl"
	{ rr->data.a.addr.s_addr <<= 8; rr->data.a.addr.s_addr |= (0xff & n); }
	break;
	case 48:
#line 405 "zone.rl"
	{ rr->data.a.addr.s_addr = htonl(rr->data.a.addr.s_addr); }
	break;
	case 50:
#line 409 "zone.rl"
	{ dns_strlcpy(rr->data.ptr.host, str, sizeof rr->data.ptr.host); }
	break;
	case 56:
#line 426 "zone.rl"
	{ dns_strlcpy(P->origin, str, sizeof P->origin); goto next; }
	break;
	case 57:
#line 428 "zone.rl"
	{ P->ttl = ttl; goto next; }
	break;
	case 58:
#line 430 "zone.rl"
	{ goto next; }
	break;
#line 1299 "zone.c"
		}
	}
	}

	_out: {}
	}

#line 464 "zone.rl"

	tok_discard(&P->toks, span);

	dns_strlcpy(P->lastrr, rr->name, sizeof P->lastrr);

	if (rr->type == DNS_T_SOA)
		P->soa = rr->data.soa;

	*soa = &P->soa;

	return rr;
} /* zone_getrr() */


size_t zone_parsesome(struct zonefile *P, const void *src, size_t len) {
	unsigned char *p = (unsigned char *)src;
	size_t lim = lengthof(P->toks.base) - P->toks.count;

	P->toks.count += fold(&P->toks.base[P->toks.count], lim, &p, &len, &P->pp);

	return p - (unsigned char *)src;
} /* zone_parsesome() */


size_t zone_parsefile(struct zonefile *P, FILE *fp) {
	unsigned char buf[1024];
	size_t tlim, lim, len;

	tlim = lengthof(P->toks.base) - P->toks.count;
	lim  = MIN(lengthof(buf), tlim);

	if (!(len = fread(buf, 1, lim, fp)))
		return 0;

	assert(len == zone_parsesome(P, buf, len));

	return len;
} /* zone_parsefile() */


struct zonefile *zone_open(const char *origin, unsigned ttl, int *error) {
	struct zonefile *P;

	if (!(P = malloc(sizeof *P)))
		{ *error = errno; return NULL; }

	zone_init(P, origin, ttl);

	return P;
} /* zone_open() */


void zone_close(struct zonefile *P) {
	free(P);
} /* zone_close() */


#if ZONE_MAIN

#include <stdlib.h>	/* EXIT_FAILURE */

#include <unistd.h>	/* getopt(3) */


struct {
	const char *progname;
} MAIN;


static void parsefile(FILE *fp, const char *origin, unsigned ttl) {
	struct zonefile P;
	struct zonerr rr;
	struct dns_soa *soa;

	zone_init(&P, origin, ttl);

	while (zone_parsefile(&P, fp)) {
		while (zone_getrr(&rr, &soa, &P)) {
			char data[512];
			dns_any_print(data, sizeof data, &rr.data, rr.type);
			printf("%s %u IN %s %s\n", rr.name, rr.ttl, dns_strtype(rr.type), data);
		}
	}
} /* parsefile() */


static void foldfile(FILE *dst, FILE *src) {
	struct zonepp state;
	unsigned char in[16], *p;
	short out[16];
	size_t len, num, i;

	memset(&state, 0, sizeof state);

	while ((len = fread(in, 1, sizeof in, src))) {
		p = in;

		while ((num = fold(out, sizeof out, &p, &len, &state))) {
			for (i = 0; i < num; i++) {
				if ((out[i] & T_LIT)
				||  (!isgraph(0xff & out[i]) && !isspace(0xff & out[i]))) {
					fprintf(dst, "\\%.3d", (0xff & out[i]));
				} else {
					fputc((0xff & out[i]), dst);
				}
			}
		}
	}
} /* foldfile() */


static void usage(FILE *fp) {
	static const char *usage =
		" [OPTIONS] [COMMAND]\n"
		"  -o ORIGIN  Zone origin\n"
		"  -t TTL     Zone TTL\n"
		"  -V         Print version info\n"
		"  -h         Print this usage message\n"
		"\n"
		"  fold       Fold into simple normal form\n"
		"  parse      Parse zone file and recompose\n"
		"\n"
		"Report bugs to William Ahern <william@25thandClement.com>\n";

	fputs(MAIN.progname, fp);
	fputs(usage, fp);
	fflush(fp);
} /* usage() */


static unsigned parsettl(const char *opt) {
	unsigned ttl;
	char *end;

	ttl = strtoul(opt, &end, 10);

	switch (tolower((unsigned char)*end)) {
	case 'w':
		ttl *= 7;
	case 'd':
		ttl *= 24;
	case 'h':
		ttl *= 60;
	case 'm':
		ttl *= 60;
	case 's':
		ttl *= 1;
	case '\0':
		break;
	default:
		fprintf(stderr, "%s: ", MAIN.progname);

		for (; *opt; opt++) {
			if (opt == end)
				fprintf(stderr, "[%c]", *opt);
			else
				fputc(*opt, stderr);
		}
		fputs(": invalid TTL\n", stderr);

		exit(EXIT_FAILURE);
	}

	return ttl;
} /* parsettl() */


#define CMD_FOLD  1
#define CMD_PARSE 2

static int command(const char *arg) {
	const char *p, *pe, *eof;
	int cs;

	arg = (arg && *arg)? arg : "parse";

	p   = arg;
	pe  = p + strlen(arg);
	eof = pe;

	
#line 1489 "zone.c"
static const char _command_actions[] = {
	0, 1, 0, 1, 1, 1, 2
};

static const char _command_key_offsets[] = {
	0, 0, 2, 3, 4, 5, 6, 7, 
	8, 9, 9
};

static const char _command_trans_keys[] = {
	102, 112, 111, 108, 100, 97, 114, 115, 
	101, 0
};

static const char _command_single_lengths[] = {
	0, 2, 1, 1, 1, 1, 1, 1, 
	1, 0, 0
};

static const char _command_range_lengths[] = {
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0
};

static const char _command_index_offsets[] = {
	0, 0, 3, 5, 7, 9, 11, 13, 
	15, 17, 18
};

static const char _command_trans_targs[] = {
	2, 5, 0, 3, 0, 4, 0, 9, 
	0, 6, 0, 7, 0, 8, 0, 10, 
	0, 0, 0, 0
};

static const char _command_trans_actions[] = {
	0, 0, 1, 0, 1, 0, 1, 0, 
	1, 0, 1, 0, 1, 0, 1, 0, 
	1, 1, 1, 0
};

static const char _command_eof_actions[] = {
	0, 1, 1, 1, 1, 1, 1, 1, 
	1, 3, 5
};

static const int command_start = 1;
static const int command_first_final = 9;
static const int command_error = 0;

static const int command_en_main = 1;


#line 1543 "zone.c"
	{
	cs = command_start;
	}

#line 1548 "zone.c"
	{
	int _klen;
	unsigned int _trans;
	const char *_acts;
	unsigned int _nacts;
	const char *_keys;

	if ( p == pe )
		goto _test_eof;
	if ( cs == 0 )
		goto _out;
_resume:
	_keys = _command_trans_keys + _command_key_offsets[cs];
	_trans = _command_index_offsets[cs];

	_klen = _command_single_lengths[cs];
	if ( _klen > 0 ) {
		const char *_lower = _keys;
		const char *_mid;
		const char *_upper = _keys + _klen - 1;
		while (1) {
			if ( _upper < _lower )
				break;

			_mid = _lower + ((_upper-_lower) >> 1);
			if ( (*p) < *_mid )
				_upper = _mid - 1;
			else if ( (*p) > *_mid )
				_lower = _mid + 1;
			else {
				_trans += (unsigned int)(_mid - _keys);
				goto _match;
			}
		}
		_keys += _klen;
		_trans += _klen;
	}

	_klen = _command_range_lengths[cs];
	if ( _klen > 0 ) {
		const char *_lower = _keys;
		const char *_mid;
		const char *_upper = _keys + (_klen<<1) - 2;
		while (1) {
			if ( _upper < _lower )
				break;

			_mid = _lower + (((_upper-_lower) >> 1) & ~1);
			if ( (*p) < _mid[0] )
				_upper = _mid - 2;
			else if ( (*p) > _mid[1] )
				_lower = _mid + 2;
			else {
				_trans += (unsigned int)((_mid - _keys)>>1);
				goto _match;
			}
		}
		_trans += _klen;
	}

_match:
	cs = _command_trans_targs[_trans];

	if ( _command_trans_actions[_trans] == 0 )
		goto _again;

	_acts = _command_actions + _command_trans_actions[_trans];
	_nacts = (unsigned int) *_acts++;
	while ( _nacts-- > 0 )
	{
		switch ( *_acts++ )
		{
	case 0:
#line 647 "zone.rl"
	{
			fprintf(stderr, "%s: %s: invalid command\n", MAIN.progname, arg);
			usage(stderr);
			exit(EXIT_FAILURE);
		}
	break;
#line 1629 "zone.c"
		}
	}

_again:
	if ( cs == 0 )
		goto _out;
	if ( ++p != pe )
		goto _resume;
	_test_eof: {}
	if ( p == eof )
	{
	const char *__acts = _command_actions + _command_eof_actions[cs];
	unsigned int __nacts = (unsigned int) *__acts++;
	while ( __nacts-- > 0 ) {
		switch ( *__acts++ ) {
	case 0:
#line 647 "zone.rl"
	{
			fprintf(stderr, "%s: %s: invalid command\n", MAIN.progname, arg);
			usage(stderr);
			exit(EXIT_FAILURE);
		}
	break;
	case 1:
#line 653 "zone.rl"
	{ return CMD_FOLD; }
	break;
	case 2:
#line 654 "zone.rl"
	{ return CMD_PARSE; }
	break;
#line 1661 "zone.c"
		}
	}
	}

	_out: {}
	}

#line 661 "zone.rl"


	return 0;
} /* command() */


int main(int argc, char **argv) {
	extern int optind;
	extern char *optarg;
	int opt;
	const char *origin = ".";
	unsigned ttl = 3600;

	MAIN.progname = argv[0];

	while (-1 != (opt = getopt(argc, argv, "o:t:Vh"))) {
		switch (opt) {
		case 'o':
			origin = optarg;

			break;
		case 't':
			ttl = parsettl(optarg);

			break;
		case 'h':
			usage(stdout);

			return 0;
		default:
			usage(stderr);

			return EXIT_FAILURE;
		} /* switch() */
	} /* getopt() */

	argc -= optind;
	argv += optind;

	switch (command(argv[0])) {
	case CMD_FOLD:
		foldfile(stdout, stdin);
		break;
	case CMD_PARSE:
		parsefile(stdin, origin, ttl);
		break;
	}

	return 0;
} /* main() */

#endif /* ZONE_MAIN */


#if __clang__
#pragma clang diagnostic pop
#elif (__GNUC__ == 4 && __GNUC_MINOR__ >= 6) || __GNUC__ > 4
#pragma GCC diagnostic pop
#endif
