/* Copyright (C) 2010-2013, Armin Biere, JKU Linz. */
/* Copyright (C) 2011-2013, Martina Seidl, JKU Linz. */

#include <assert.h>
#include <ctype.h>
#include <limits.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/time.h>
#include <sys/resource.h>
#include <unistd.h>
#include <signal.h>
#include <time.h>
#include "bloqqer.h"

#ifdef SOLVER
  #include "qdpll.h"
#endif 


extern const char *blqr_id (void);
extern const char *blqr_version (void);
extern const char *blqr_cflags (void);

#define COVER(COVER_CONDITION) \
do { \
  if (!(COVER_CONDITION)) break; \
  fprintf (stderr, \
           "*BLOQQER* covered line %d: %s\n", \
	   __LINE__, # COVER_CONDITION); \
  if (getenv("NCOVER")) break; \
  abort (); \
} while (0)


/******** logging macros ***********/


#ifdef NLOG
#define LOG(...) do { } while (0)
#define LOGCLAUSE(...) do { } while (0)
#else
static int loglevel;
#define LOGPREFIX "c [BLOQQER] "
#define LOG(FMT,ARGS...) \
  do { \
    if (loglevel <= 0) break; \
    fputs (LOGPREFIX, stdout); \
    fprintf (stdout, FMT, ##ARGS); \
    fputc ('\n', stdout); \
    fflush (stdout); \
  } while (0)
#define LOGCLAUSE(CLAUSE,FMT,ARGS...) \
  do { \
    Node * LOGCLAUSE_P; \
    if (loglevel <= 0) break; \
    fputs (LOGPREFIX, stdout); \
    fprintf (stdout, FMT, ##ARGS); \
    for (LOGCLAUSE_P = (CLAUSE)->nodes; LOGCLAUSE_P->lit; LOGCLAUSE_P++) \
      fprintf (stdout, " %d", LOGCLAUSE_P->lit); \
    fputc ('\n', stdout); \
    fflush (stdout); \
  } while (0)
#endif


/******** memory management macros ***********/


#define INC(B) \
  do { \
    current_bytes += B; \
    if (max_bytes < current_bytes) \
      max_bytes = current_bytes; \
  } while (0)
#define DEC(B) \
  do { \
    assert (current_bytes >= B); \
    current_bytes -= B; \
  } while (0)
#define NEWN(P,N) \
  do { \
    size_t NEWN_BYTES = (N) * sizeof *(P); \
    (P) = malloc (NEWN_BYTES); \
    if (!(P)) die ("out of memory"); \
    assert (P); \
    memset ((P), 0, NEWN_BYTES); \
    INC (NEWN_BYTES); \
  } while (0)
#define DELN(P,N) \
  do { \
    size_t DELN_BYTES = (N) * sizeof *(P); \
    DEC (DELN_BYTES); \
    free (P); \
  } while (0)
#define RSZ(P,M,N) \
  do { \
    size_t RSZ_OLD_BYTES = (M) * sizeof *(P); \
    size_t RSZ_NEW_BYTES = (N) * sizeof *(P); \
    DEC (RSZ_OLD_BYTES); \
    (P) = realloc (P, RSZ_NEW_BYTES); \
    if (RSZ_OLD_BYTES > 0 && !(P)) die ("out of memory"); \
    assert (P); \
    if (RSZ_NEW_BYTES > RSZ_OLD_BYTES) { \
      size_t RSZ_INC_BYTES = RSZ_NEW_BYTES - RSZ_OLD_BYTES; \
      memset (RSZ_OLD_BYTES + ((char*)(P)), 0, RSZ_INC_BYTES); \
    } \
    INC (RSZ_NEW_BYTES); \
  } while (0)
#define NEW(P) NEWN((P),1)
#define DEL(P) DELN((P),1)



/******** qrat tracing macros ***********/


#define QRAT_TRACE_RATA_UNIT(LIT,MSG) \
  do { \
    if (qrat_file && do_qrat) { \
      if (qrat_msg)  fprintf (qrat_file, "%d 0 %s\n",LIT,MSG); \
      else fprintf (qrat_file, "%d 0\n",LIT); \
    } \
    qrat_lit = 0;\
  } while (0)

#define QRAT_TRACE_BLE_FROM_CLAUSE(LIT, CLAUSE,MSG) \
  do { \
    if (qrat_file && do_qrat) { \
      if (is_trivial_clause (CLAUSE)) {\
        qrat_lit = 0; \
        break; \
      } \
      Node * TCLAUSE_P; \
      fprintf (qrat_file, "u %d ",LIT); \
      for (TCLAUSE_P = (CLAUSE)->nodes; TCLAUSE_P->lit; TCLAUSE_P++) \
      if (TCLAUSE_P->lit != LIT) fprintf (qrat_file, "%d ", TCLAUSE_P->lit); \
      if (!qrat_msg) fprintf(qrat_file,"0\n"); \
      else fprintf(qrat_file,"0 %s\n",MSG); \
      qrat_lit = 0; \
    } \
  } while (0)

#define QRAT_TRACE_EUR_FROM_STACK0(LIT,MSG) \
  do { \
    if (qrat_file && do_qrat && !lookup_clause ()) { \
      if (is_trivial_on_stack ()) {\
        qrat_lit = 0; \
        break; \
      } \
      fprintf (qrat_file, "u %d ",LIT); \
      qrat_lit = LIT; \
      qrat_trace_stack0 (); \
      if (!qrat_msg) fprintf(qrat_file,"0\n"); \
      else fprintf(qrat_file,"0 %s\n",MSG); \
    } \
    qrat_lit = 0; \
  } while (0)

#define QRAT_TRACE_EUR_FROM_CLAUSE(LIT, CLAUSE,MSG) \
  do { \
    if (qrat_file && do_qrat) { \
      if (is_trivial_clause (CLAUSE)) {\
        qrat_lit = 0; \
        break; \
      } \
      Node * TCLAUSE_P; \
      fprintf (qrat_file, "u %d ",LIT); \
      for (TCLAUSE_P = (CLAUSE)->nodes; TCLAUSE_P->lit; TCLAUSE_P++) \
        if (TCLAUSE_P->lit != LIT) fprintf (qrat_file, "%d ", TCLAUSE_P->lit); \
      if (!qrat_msg) fprintf(qrat_file,"0\n"); \
      else fprintf(qrat_file,"0 %s\n",MSG); \
      qrat_lit = 0; \
    } \
  } while (0)

#define QRAT_TRACE_RATE_FROM_CLAUSENODES(NODE,MSG) \
  do { \
    if (qrat_file && do_qrat) { \
      Node * TCLAUSE_P; \
      if (qrat_lit) { \
         fprintf (qrat_file, "d %d ",qrat_lit); \
      } \
      else fprintf (qrat_file, "d "); \
      for (TCLAUSE_P = NODE; TCLAUSE_P->lit; TCLAUSE_P++) \
       if (TCLAUSE_P->lit != qrat_lit) fprintf (qrat_file, "%d ", TCLAUSE_P->lit); \
      if (!qrat_msg) fprintf(qrat_file,"0\n"); \
      else fprintf(qrat_file,"0 %s\n",MSG); \
      qrat_lit = 0; \
    } \
  } while (0)

#define QRAT_TRACE_RATA_FROM_CLAUSENODES(NODE,MSG) \
  do { \
    if (qrat_file && do_qrat) { \
      Node * TCLAUSE_P; \
      if (qrat_lit) { \
         fprintf (qrat_file, "%d ",qrat_lit); \
      } \
      for (TCLAUSE_P = NODE; TCLAUSE_P->lit; TCLAUSE_P++) \
        if (TCLAUSE_P->lit != qrat_lit) fprintf (qrat_file, "%d ", TCLAUSE_P->lit); \
      if (!qrat_msg) fprintf(qrat_file,"0\n"); \
      else fprintf(qrat_file,"0 %s\n",MSG); \
      qrat_lit = 0; \
    } \
  } while (0)

#define QRAT_TRACE_RATA_FROM_CLAUSE_WITH_ARG(CLAUSE,LIT,MSG) \
  do { \
    if (qrat_file && do_qrat) { \
      if (is_trivial_clause (CLAUSE)) {\
        qrat_lit = 0; \
        break; \
      } \
      Node * TCLAUSE_P; \
      if (qrat_lit)  { \
        fprintf (qrat_file, " %d %d ",qrat_lit,LIT); \
      } else {\
        fprintf (qrat_file, " %d %d ",qrat_lit,LIT); \
      } \
      for (TCLAUSE_P = (CLAUSE)->nodes; TCLAUSE_P->lit; TCLAUSE_P++) \
        if (TCLAUSE_P->lit != qrat_lit) fprintf (qrat_file, "%d ", TCLAUSE_P->lit); \
      if (!qrat_msg) fprintf(qrat_file,"0\n"); \
      else fprintf(qrat_file,"0 %s\n",MSG); \
      qrat_lit = 0; \
    } \
  } while (0)



#define QRAT_TRACE_RATA_FROM_CLAUSE(CLAUSE,MSG) \
  do { \
    if (qrat_file && do_qrat) { \
      if (is_trivial_clause (CLAUSE)) {\
        qrat_lit = 0; \
        break; \
      } \
      Node * TCLAUSE_P; \
      if (qrat_lit)  { \
        fprintf (qrat_file, " %d ",qrat_lit); \
      } \
      for (TCLAUSE_P = (CLAUSE)->nodes; TCLAUSE_P->lit; TCLAUSE_P++) \
        if (TCLAUSE_P->lit != qrat_lit) fprintf (qrat_file, "%d ", TCLAUSE_P->lit); \
      if (!qrat_msg) fprintf(qrat_file,"0\n"); \
      else fprintf(qrat_file,"0 %s\n",MSG); \
      qrat_lit = 0; \
    } \
  } while (0)


#define QRAT_TRACE_RATE_FROM_CLAUSE_WITH_ARG(CLAUSE,LIT,MSG) \
  do { \
    if (qrat_file && do_qrat) { \
      if (is_trivial_clause (CLAUSE)) {\
        qrat_lit = 0; \
        break; \
      } \
      Node * TCLAUSE_P; \
      if (qrat_lit)  { \
        fprintf (qrat_file, "d %d %d ",qrat_lit,LIT); \
      } \
      else fprintf (qrat_file, "d %d ",LIT); \
      for (TCLAUSE_P = (CLAUSE)->nodes; TCLAUSE_P->lit; TCLAUSE_P++) \
        if (TCLAUSE_P->lit != qrat_lit) fprintf (qrat_file, "%d ", TCLAUSE_P->lit); \
      if (!qrat_msg) fprintf(qrat_file,"0\n"); \
      else fprintf(qrat_file,"0 %s\n",MSG); \
      qrat_lit = 0; \
    } \
  } while (0)


#define QRAT_TRACE_RATE_FROM_CLAUSE(CLAUSE,MSG) \
  do { \
    if (qrat_file && do_qrat) { \
      if (is_trivial_clause (CLAUSE)) {\
        qrat_lit = 0; \
        break; \
      } \
      Node * TCLAUSE_P; \
      if (qrat_lit)  { \
        fprintf (qrat_file, "d %d ",qrat_lit); \
      } \
      else fprintf (qrat_file, "d "); \
      for (TCLAUSE_P = (CLAUSE)->nodes; TCLAUSE_P->lit; TCLAUSE_P++) \
        if (TCLAUSE_P->lit != qrat_lit) fprintf (qrat_file, "%d ", TCLAUSE_P->lit); \
      if (!qrat_msg) fprintf(qrat_file,"0\n"); \
      else fprintf(qrat_file,"0 %s\n",MSG); \
      qrat_lit = 0; \
    } \
  } while (0)


#define QRAT_TRACE_TRIV_RATE_FROM_STACK0(MSG) \
  do { \
    if (qrat_file && do_qrat ) { \
      fprintf(qrat_file,"d "); \
      if (qrat_lit) { \
        fprintf(qrat_file, "%d ", qrat_lit); \
      } \
      qrat_trace_stack0 (); \
      if (!qrat_msg) fprintf(qrat_file,"0\n"); \
      else fprintf(qrat_file,"0 %s\n",MSG); \
    } \
    qrat_lit = 0; \
  } while (0)  

#define QRAT_TRACE_RATE_FROM_STACK0(MSG) \
  do { \
    if (qrat_file && do_qrat ) { \
      if (is_trivial_on_stack ()) {\
        qrat_lit = 0; \
        break; \
      } \
      fprintf(qrat_file,"d "); \
      if (qrat_lit) { \
        fprintf(qrat_file, "%d ", qrat_lit); \
      } \
      qrat_trace_stack0 (); \
      if (!qrat_msg) fprintf(qrat_file,"0\n"); \
      else fprintf(qrat_file,"0 %s\n",MSG); \
    } \
    qrat_lit = 0; \
  } while (0)  

#define QRAT_TRACE_RATE_FROM_STACK(START_IGNORE,IGNORE_OFFSET,MSG) \
  do { \
    if (qrat_file && do_qrat ) { \
      if (is_trivial_on_stack ()) {\
        qrat_lit = 0; \
        break; \
      } \
      fprintf(qrat_file,"d "); \
       if (qrat_lit) { \
         fprintf(qrat_file, "%d ", qrat_lit); \
      } \
      qrat_trace_stack (START_IGNORE, IGNORE_OFFSET);  \
      if (!qrat_msg) fprintf(qrat_file,"0\n"); \
      else fprintf(qrat_file,"0 %s\n",MSG); \
    } \
    qrat_lit = 0; \
  } while (0)  

#define QRAT_TRACE_BLE_FROM_STACK(LIT,START_IGNORE,IGNORE_OFFSET,MSG) \
  do { \
    if (qrat_file && do_qrat) { \
      if (is_trivial_on_stack ()) {\
        qrat_lit = 0; \
        break; \
      } \
      fprintf(qrat_file,"u %d ", lit); \
      qrat_lit = LIT; \
      qrat_trace_stack (START_IGNORE, IGNORE_OFFSET);  \
      if (!qrat_msg) fprintf(qrat_file,"0\n"); \
      else fprintf(qrat_file,"0 %s\n",MSG); \
      qrat_lit = 0;\
    } \
  } while (0)  

#define QRAT_TRACE_RATA_FROM_STACK0_WITHOUT_CHECK(MSG) \
  do { \
    if (qrat_file) { \
      if (qrat_lit) { \
        fprintf(qrat_file, "%d ", qrat_lit); \
      } \
      qrat_trace_stack0 (); \
      if (!qrat_msg) fprintf(qrat_file,"0\n"); \
      else fprintf(qrat_file,"0 %s\n",MSG); \
    } \
    qrat_lit = 0; \
  } while (0)  


#define QRAT_TRACE_RATA_FROM_STACK0(MSG) \
  do { \
    if (qrat_file && do_qrat && !lookup_clause()) { \
      if (is_trivial_on_stack ()) {\
        qrat_lit = 0; \
        break; \
      } \
      if (qrat_lit) { \
        fprintf(qrat_file, "%d ", qrat_lit); \
      } \
      qrat_trace_stack0 (); \
      if (!qrat_msg) fprintf(qrat_file,"0\n"); \
      else fprintf(qrat_file,"0 %s\n",MSG); \
    } \
    qrat_lit = 0; \
  } while (0)  

#define QRAT_TRACE_RATA_FROM_STACK(START_IGNORE,IGNORE_OFFSET,MSG) \
  do { \
    if (qrat_file && do_qrat && !lookup_clause_without (START_IGNORE, IGNORE_OFFSET)) { \
      if (is_trivial_on_stack ()) {\
        qrat_lit = 0; \
        break; \
      } \
      if (qrat_lit) { \
        fprintf(qrat_file, "%d ", qrat_lit); \
      } \
      qrat_trace_stack (START_IGNORE, IGNORE_OFFSET);  \
      if (!qrat_msg) fprintf(qrat_file,"0\n"); \
      else fprintf(qrat_file,"0 %s\n",MSG); \
      qrat_lit = 0; \
    } \
  } while (0)  

#define QRAT_TRACE_RATA_FROM_STACK_WITHOUT_LIT(LIT,MSG) \
  do { \
    if (qrat_file && do_qrat && !lookup_clause ()) { \
      if (is_trivial_on_stack ()) {\
        qrat_lit = 0; \
        break; \
      } \
      int QRAT_TRACE_TIDX; \
      if (qrat_lit) { \
        fprintf(qrat_file, "%d ", qrat_lit); \
      } \
      for (QRAT_TRACE_TIDX=0; QRAT_TRACE_TIDX<num_lits; QRAT_TRACE_TIDX++) {\
        if (lits[QRAT_TRACE_TIDX] != LIT) \
          fprintf(qrat_file, "%d ",lits[QRAT_TRACE_TIDX]); \
      } \
      if (!qrat_msg) fprintf(qrat_file,"0\n"); \
      else fprintf(qrat_file,"0 %s\n",MSG); \
      qrat_lit = 0; \
    }\
  } while (0)  




typedef unsigned long long Sig;

typedef struct Occ {		/* occurrence list anchor */
  int count;
  struct Node * first, * last;
} Occ;

typedef enum Tag {
  FREE = 0,
  UNET = 1,
  UNATE = 2,
  FIXED = 3,
  ZOMBIE = 4,
  ELIMINATED = 5,
  SUBSTITUTED = 6,
  EXPANDED = 7,
  SOLVING = 8,
  FORALL_RED = 9,
  UNIT = 10,
} Tag;

typedef struct Var {
  struct Scope * scope;
  Tag tag;
  int lmark, lmark2; 		/* marks for lookup */
  int mark, mark2, mark3,mark4;	/* primary mark flag */
  int submark;			/* second subsumption mark flag */
  int mapped;			/* index mapped to */
  int fixed;			/* assignment */
  int score, pos;		/* for elimination priority queue */
  int expcopy;			/* copy in expansion */
  struct Var * prev, * next;	/* scope variable list links */
  Occ occs[2];			/* positive and negative occurrence lists */
} Var;

typedef struct Scope {
  int type;			/* type>0 == existential, type<0 universal */
  int order;			/* scope order: outer most = 0 */
  int free;			/* remaining free variables */
  int stretch;			/* stretches to this scope */
  struct Var * first, * last;	/* variable list */
  struct Scope * outer, * inner;
} Scope;

typedef struct Node {		/* one 'lit' occurrence in a 'clause' */
  int lit;
  int blocked; 			/* 1 if used as pivot of blocked clause */
  struct Clause * clause;
  struct Node * prev, * next;	/* links all occurrences of 'lit' */
} Node;

typedef struct Anchor {		/* list anchor for forward watches */
  int count;
  struct Clause * first, * last;
} Anchor;

typedef struct Watch {		/* watch for forward subsumption */
  int idx;			/* watched 'idx' */
  struct Clause * prev, * next;	/* links for watches of 'idx' */
} Watch;

typedef struct Clause {
  int size;
  int mark, cmark2;
  int count; 
  Sig sig;			/* subsumption/strengthening signature */
  struct Clause * prev, * next;	/* chronlogical clause list links */
  struct Clause * head, * tail;	/* backward subsumption queue links */
  Watch watch;			/* forward subsumption watch */
  Node nodes[1];		/* embedded literal nodes */
} Clause;

typedef struct Opt {
  char inc;
  const char * name;
  int def, low, high;
  const char * description;
  int * valptr;
} Opt;


typedef struct StrOpt {
  const char * name;
  const char * description;
  const char ** valptr;
} StrOpt;

static int verbose, bce, ble, eq, ve, quantifyall, force, strict, keep, output;
static int help, range, defaults, bound, hte, htesize, hteoccs, htesteps;
static int embedded, ignore, cce, hbce, hble, exp, axcess, splitlim;
static int fwmaxoccs, fwmax1size, fwmax2size;
static int bwmaxoccs, bwmax1size, bwmax2size;
static int blkmax1occs, blkmax2occs;
static int blkmax1size, blkmax2size;
static int elimoccs, elimsize, excess;
static int timelimit;
static int implicit_scopes_inited;
static int partial_assignment;
static int assigned_scope = -1;
static int guessnumber;
static const char * qrat_trace;
#ifdef SOLVER 
static int depqbf_on;
static QDPLL *qdpll;
#endif
static int qrat_lit, qrat_msg = 1;
static void flush (int );
static void check_all_unmarked (void);
static Clause * lookup_clause ();
static int least_occuring_lit ();
static int least_occuring_lit_without (int, int);
static int do_qrat = 1;
static int parsing = 0;
static void add_var(int, Scope *);
static void enlarge_vars(int);
static void delete_clause(Clause *);
static void delete_node(Node *);
static void add_node(Clause *, Node *, int);
static void print_clauses(FILE *);
static int print_scope(Scope *, FILE *, int);
static int var2lit(Var *);
static void qrat_trace_stack0 (void);
static void qrat_trace_stack (int, int);
static void print_clause (Clause *, FILE *);
static void block_lit (int);
static int trail_flushed (void);

static void push_stack (int elem);
static int is_trivial_on_stack () ;
static int is_trivial_clause (Clause *) ;
static void flush_vars (); 
static FILE * qrat_file;
static void push_literal (int); 
static int univ_mini;
#define IM INT_MAX
static StrOpt str_opts [] = {
{"qrat","generate QRAT trace",&qrat_trace},
{0,0}
};

static Opt opts[] = {
{'h',"help",0,0,1,"command line options summary",&help},
#ifdef SOLVER
{'s',"depqbf",1,0,1,"solve formula with DepQBF",&depqbf_on},
#endif
#ifndef NLOG
{'l',"log",0,0,1,"set logging level",&loglevel},
#endif
{'v',"verbose",0,0,2,"set verbosity level",&verbose},
{'i',"ignore",0,0,1,"ignore embedded options",&ignore},
{000,"output",1,0,1,"do not print preprocessed CNF",&output},
{'d',"defaults",0,0,1,"print command line option default values",&defaults},
{'e',"embedded",0,0,1,"as '-d' but in embedded format",&embedded},
{'r',"range",0,0,1,"print comand line option value ranges",&range},
{'k',"keep",1,0,1,"keep original variable indices",&keep},
{'f',"force",0,0,1,"force reading if clause number incorrect",&force},
{'q',"quantify-all",1,0,1,"quantify all variables in output",&quantifyall},
{'m',"partial-assignment",0,0,1,"show assignment of first quantifier block",&partial_assignment},
{'u',"exp-mini",1,0,1,"miniscoping during expansion",&univ_mini},
{000,"timeout",0,0,IM,"set time limit",&timelimit},
{000,"guess",0,0,IM,"guess random univ. expansions",&guessnumber},
{000,"split",512,3,IM,"split long clauses of at least this length",&splitlim},
{000,"bce",1,0,1,"enable blocked clause elimination",&bce},
{000,"ble",1,0,1,"enable blocked literal elimination",&ble},
{000,"eq",1,0,1,"enable equivalent literal reasoning",&eq},
{000,"ve",1,0,1,"enable variable elimination",&ve},
{000,"exp",1,0,1,"enable variable expansion",&exp},
{000,"hte",1,0,1,"enable hidden clause elimination",&hte},
{000,"cce",1,0,1,"enable covered literal addition",&cce},
{000,"hbce",1,0,1,"enable hidden blocked clause elimination",&hbce},
{000,"hble",0,0,1,"enable asymmetrick blocked literal  elimination",&hble},
{'s',"strict",0,0,1,"enforce strict variable elimination",&strict},
{000,"excess",20,-IM,IM,"excess limit in variable elimination",&excess},
{000,"axcess",2000,-IM,IM,"excess limit in variable expansion",&axcess},
{000,"fwmaxoccs",32,0,IM,"forward max occurrences",&fwmaxoccs},
{000,"fwmax1size",32,0,IM,"inner forward max clause size", &fwmax1size},
{000,"fwmax2size",64,0,IM,"outer forward max clause size", &fwmax2size},
{000,"bwmaxoccs",16,0,IM,"backward max occurrences",&bwmaxoccs},
{000,"bwmax1size",16,0,IM,"inner backward max clause size", &bwmax1size},
{000,"bwmax2size",32,0,IM,"outer backward max clause size", &bwmax2size},
{000,"blkmax1occs",32,0,IM,"inner max blocking lit occs",&blkmax1occs},
{000,"blkmax2occs",16,0,IM,"outer max blocking lit occs",&blkmax2occs},
{000,"blkmax1size",32,0,IM,"inner max blocked clause size",&blkmax1size},
{000,"blkmax2size",16,0,IM,"outer max blocked clause size",&blkmax2size},
{000,"elimoccs",32,0,IM,"max eliminated variable occs",&elimoccs},
{000,"elimsize",32,0,IM,"max eliminated clauses size",&elimsize},
{000,"bound",1024,-1,IM,"bound for all bw/fw/block/elim limits",&bound},
{000,"htesteps",64,0,IM,"hte steps bound",&htesteps},
{000,"hteoccs",32,0,IM,"hte max occurrences size",&hteoccs},
{000,"htesize",1024,2,IM,"hte max clause size",&htesize},
{000,0},
};

static int remaining_clauses_to_parse;
static int lineno = 1;

static int terminal, notclean;
static struct itimerval timer, old_timer;
static const char * timerstr;
static int * timerptr;
static void (*old_alarm_handler)(int);

static Scope * inner_most_scope, * outer_most_scope;
static Clause * first_clause, * last_clause, * empty_clause, * queue;
static int nqueue;

static int num_vars, orig_num_vars, fixed, elimidx, substituting = 0, substituting2 = 0;
static int no_lookup = 0;
static int expanding = 0;
static int universal_vars, existential_vars, implicit_vars;
static int * schedule, size_schedule;
static int * trail, * top_of_trail, * next_on_trail;
static int * dfsi, * mindfsi, * repr, * subst_vals;
static Sig * fwsigs, * bwsigs;
static int ** clause_stack;
static int clause_stack_size, clause_stack_top;
static Anchor * anchors;
static Var * vars;

static int nstack, szstack, * stack;
static int num_lits, size_lits, * lits;
static int naux, szaux, * aux;
static int nline, szline;
static char * line;

static size_t current_bytes, max_bytes;
static int embedded_options, command_line_options;
static int added_clauses, added_binary_clauses, enqueued_clauses, pushed_vars;
static int subsumed_clauses, strengthened_clauses;
static int forward_subsumed_clauses, forward_strengthened_clauses;
static int backward_subsumed_clauses, backward_strengthened_clauses;
static int blocked_clauses, blocked_lits, orig_clauses, num_clauses, hidden_tautologies;
static int units, unates, unets, zombies, eliminated, remaining, mapped,
outermost_blocked;
static int substituted, eqrounds, nonstrictves, hidden_blocked_clauses;
static int hidden_blocked_literals;
static int added_binary_clauses_at_last_eqround;
static int expanded, expansion_cost_mark;
static struct { struct { int64_t lookups, hits; } sig1, sig2; } fw, bw;
static long long hlas, clas;
static Clause * cl_iterator;
static Node * lit_iterator;

static double bceTime = 0, eqTime = 0, veTime = 0, cceTime = 0, hteTime = 0;
static double hbceTime = 0, splitTime = 0, expTime = 0, subsTime = 0;
static double univredTime = 0, strengthTime = 0, trivclauseTime = 0;
static double parseTime = 0, pureTime = 0;
static double elimTime = 0, flushTime = 0;
static void unmark2_lits (void);
static void unmark_lits (void);
static Sig sig_lits_without (int, int, int*, int);
static Sig sig_lits2 (int *, int);
static Clause * lookup_clause_without (int, int);


static int print_progress (void) { 
#ifndef NLOG
  if (loglevel) return 0;
#endif
  if (verbose < 2) return 0;
  return terminal;
}

static void progress_handler (int s) {
  char buffer[80];
  int len;
  assert (s == SIGALRM);
  assert (timerstr);
  if (!timerstr || !timerptr) return;
  sprintf (buffer, "c [bloqqer] %s %d", timerstr, *timerptr);
  notclean = 1;
  fputs (buffer, stdout);
  len = strlen (buffer);
  while (len++ < 70) putc (' ', stdout);
  putc ('\r', stdout);
  fflush (stdout);
}

static void start_progress (const char * msg, int * ptr) {
  if (!print_progress ()) return;
  assert (msg);
  assert (ptr);
  timer.it_interval.tv_sec = 0;
  timer.it_interval.tv_usec = 10000;
  timer.it_value = timer.it_interval;
  old_alarm_handler = signal (SIGALRM, progress_handler);
  setitimer (ITIMER_REAL, &timer, &old_timer);
  assert (!timerstr);
  assert (!timerptr);
  timerstr = msg;
  timerptr = ptr;
}

static void clr_progress_handler () {
  signal (SIGALRM, old_alarm_handler);
  assert (timerstr);
  timerstr = 0;
  timerptr = 0;
  setitimer (ITIMER_REAL, &old_timer, 0);
}

static void clean_line (void) {
  int i;
  if (!notclean) return;
  fputc ('\r', stdout);
  for (i = 0; i < 70; i++) fputc (' ', stdout);
  fputc ('\r', stdout);
  fflush (stdout);
  notclean = 0;
}

static void stop_progress (void) {
  if (!print_progress ()) return;
  clr_progress_handler ();
  clean_line ();
}

static void die (const char * fmt, ...) {
  va_list ap;
  if (timerstr) stop_progress ();
  fputs ("*** bloqqer: ", stderr);
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  fflush (stderr);
  exit (1);
}



static void sigalrm_handler(int sig) {
  die("out of time");
}

static void set_signal_handlers() {

  signal (SIGALRM, sigalrm_handler);

}

static void msg (const char * fmt, ...) {
  va_list ap;
  if (!verbose) return;
  if (notclean) clean_line ();
  fputs ("c [bloqqer] ", stdout);
  va_start (ap, fmt);
  vfprintf (stdout, fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

static void wrn (const char * fmt, ...) {
  va_list ap;
  if (notclean) clean_line ();
  fputs ("c *bloqqer* ", stdout);
  va_start (ap, fmt);
  vfprintf (stdout, fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

static double seconds (void) {
  struct rusage u;
  double res;
  if (getrusage (RUSAGE_SELF, &u)) return 0;
  res = u.ru_utime.tv_sec + 1e-6 * u.ru_utime.tv_usec;
  res += u.ru_stime.tv_sec + 1e-6 * u.ru_stime.tv_usec;
  return res;
}



static Var * lit2var (int lit) {
  assert (lit && abs (lit) <= num_vars);
  return vars + abs (lit);
}


static void qrat_trace_stack (int min, int offset) {
  int lit, i;
  Var * v;

  for (i=0; i < num_lits; i++) {
    if ((i >= min) && (i < min+offset)) continue;
    lit = lits[i];
    v = lit2var (lit);
    if (v->mark2) {
      continue;
    } else {
      if (v->mark3) {
        if (v->mark3 == lit) continue;
        v->mark2 = lit;
      } else {
        v->mark3 = lit;
      }
    }
    if (lit != qrat_lit) fprintf(qrat_file,"%d ",lit);
  }
  unmark2_lits ();
}



static void qrat_trace_stack0 (void) {
  int lit, i;
  Var * v;
  unmark2_lits();
  for (i=0; i < num_lits; i++) {
    lit = lits[i];
    v = lit2var (lit);
    if (v->mark2) {
      continue;
    } else {
      if (v->mark3) {
        if (v->mark3 == lit) continue;
        v->mark2 = lit;
      } else {
        v->mark3 = lit;
      }
    }
    
    if (lit != qrat_lit) {
      fprintf(qrat_file,"%d ",lit);
    }

  }
  unmark2_lits ();
}

static Scope * lit2scope (int lit) {
  return lit2var (lit)->scope;
}

static int sign (int lit) {
  return lit < 0 ? -1 : 1;
}

#ifndef NLOG
static const char * type2str (int type) {
  return type < 0 ? "universal" : "existential";
}
#endif


static void add_outer_most_scope (void) {
  NEW (outer_most_scope);
  outer_most_scope->type = 1;
  inner_most_scope = outer_most_scope;
  LOG ("new outer most existential scope 0");
}

static void add_var (int idx, Scope * scope) {
  Var * v;
  assert (0 < idx && idx <= num_vars);
  v = lit2var (idx);
  assert (!v->scope);
  v->scope = scope;
  v->next = NULL;
  v->prev = scope->last;


  if (scope->last) scope->last->next = v;
  else scope->first = v;
  scope->last = v;
  LOG ("adding %s variable %d to %s scope %d",
       type2str (scope->type), idx, type2str (scope->type), scope->order);
  assert (v->tag == FREE);
  scope->free++;
}

static void add_quantifier (int lit) {
  Scope * scope;
  if (!outer_most_scope) 
    add_outer_most_scope ();
  if (inner_most_scope->type != sign (lit)) {
    
    NEW (scope);
    scope->outer = inner_most_scope;
    scope->type = sign (lit);
    scope->order = inner_most_scope->order + 1;
    scope->stretch = scope->order;
    inner_most_scope->inner = scope;
    inner_most_scope = scope;
    LOG ("new inner %s scope %d", type2str (scope->type), scope->order);
  } else scope = inner_most_scope;
  add_var (abs (lit), scope);
}

static size_t bytes_clause (int size) {
  return sizeof (Clause) + size * sizeof (Node);
}

static int existential (int lit) {
  return lit2scope (lit)->type > 0;
}

static int universal (int lit) {
  return lit2scope (lit)->type < 0;
}

static int lit2order (int lit) {
  return lit2scope (lit)->order;
}

static int deref (int lit) {
  Var * v = lit2var (lit);
  int res = v->fixed;
  if (lit < 0) res = -res;
  return res;
}

static Occ * lit2occ (int lit) {
  Var * v = lit2var (lit);
  return v->occs + (lit < 0);
}

static void tag_var (Var * v, Tag tag) {
  Scope * scope;
  assert (v->tag == FREE);
  assert (tag != FREE);
  v->tag = tag;
  scope = v->scope;
  assert (scope->free > 0);
  scope->free--;
#ifndef NLOG
  if (!scope->free) LOG ("scope %d becomes empty", scope->order);
#endif
}


static void tag_lit (int lit, Tag tag) { tag_var (lit2var (lit), tag); }

static void forall_reduce_clause (void) {
  int i, j, lit, order, tmp;
  double start = seconds();
  int unsat = 0;
  order = 0;
  for (i = 0; i < num_lits; i++) {
    lit = lits[i];
    assert (!deref (lit));
    if (universal (lit)) continue;
    tmp = lit2order (lit);
    if (tmp <= order) continue;
    order = tmp;
  }
  j = 0;
  if (partial_assignment && assigned_scope == 1 && order == 0) unsat = 1;
  for (i = 0; i < num_lits; i++) {
    lit = lits[i];
    if (existential (lit) || lit2order (lit) < order) lits[j++] = lit; 
    else {
      assert (!expanding);
      if (!lookup_clause_without (j, i+1-j)) {
        QRAT_TRACE_BLE_FROM_STACK (lit,j,i-j,"universal reduction");
      } else {
        QRAT_TRACE_RATE_FROM_STACK (j,i-j,"universal reduction subs");
      }
      if (unsat) {
        tag_lit (lit, FORALL_RED);
        vars [abs(lit)].fixed = -lit;
      }
    }
  }
  num_lits = j;
  univredTime += (seconds() - start);
}

static int is_trivial_on_stack () {
  int i, lit; 
  Var * v;
  int trivial = 0;

  if (empty_clause) return 1;

  for (i=0; i<num_lits; i++) {
    lit = lits[i];
    v = lit2var (lit);
    if (v->mark2 == -lit) {
      trivial = 1;
      break;
    } else {
      v->mark2 = lit;
    }
  }
  for (i=0; i<num_lits; i++) {
    lit = lits[i];
    v = lit2var (lit);
    v->mark2 = 0;
  }

  return trivial;
}

static int is_trivial_clause (Clause * c) {
  Node * n;
  int  trivial = 0;
  int lit;
  Var * v;

  if (empty_clause) return 1;


  for (n=c->nodes;(lit = n->lit); n++) {
    v = lit2var (lit);
    if (v->mark2 == -lit) {
      trivial = 1;
      break;
    } else {
      v->mark2 = lit;
    }
  }

  
  for (n=c->nodes;(lit = n->lit); n++) {
    v = lit2var (lit);
    v->mark2 = 0;
  }

  return trivial;

}

static int is_sat () {
 int i; 
 int tmp, lit;
  for (i=0; i<num_lits;i++) {
    lit = lits[i];
    tmp = deref (lit);
    if (tmp > 0) return 1;
  }

  return 0;

}

static int trivial_clause_ (int parsing) {

  int i, j, trivial, lit, tmp, elim_lit;
  double start = seconds();
  int taut = is_trivial_on_stack ();

  Var * v;
  trivial = j = 0;
  int final_rm = 0, rm = 0;


  if (lookup_clause ()) {
     if (parsing) {
	QRAT_TRACE_RATE_FROM_STACK0 ("clause twice in input");
     }
     return 1;
  }

  if (taut) {
     if (parsing) {
	QRAT_TRACE_TRIV_RATE_FROM_STACK0("tautological clause");
     }
    return 1;
  }



  for (i = 0; !trivial && i < num_lits; i++) {
    lit = lits[i];		// satisfied clause
    tmp = deref (lit);
    if (tmp > 0) {
      elim_lit = lit;
      trivial = 1;
      break;
    }
    else if (!tmp) {
      v = lit2var (lit);	// tautological clause
      if (v->mark == -lit) {
        elim_lit = lit;
        trivial = 1;
        taut = 1;
        break;
      } else if (!v->mark) {	// keep literal
        lits[j++] = lit;
        v->mark = lit;
      }
      // double literals are eliminated here - do nothing here 
    } else {
      if (!taut) {		// remove literal
        v = lit2var (lit);
        if (v->scope->type > 0) {	// existential lit
          if (!lookup_clause_without (j, i+1-j)) {
            qrat_lit = 0;
            int next;
            if (j == 0) next = i+1;
            else next = 0;
            if (!(((j+abs(i+1-num_lits)) == 1) && 
                ((lit2var(lits[next])->tag != FREE) && 
                (lit2var(lits[next])->fixed == lits[next])))) {
              QRAT_TRACE_RATA_FROM_STACK(j,i+1-j,"trivial clause");
              final_rm = 1;
            }
          }
          if (((j+abs(i-num_lits)) >= 1) && !lookup_clause_without(j,i-j)) {
            qrat_lit = lit;
	   QRAT_TRACE_RATE_FROM_STACK(j,i-j,"trivial clause assigned");
            rm = 1;
          }
        } else {			// univeral lit
          Clause * l = NULL;
          if (!(l = lookup_clause_without (j, i+1-j))) {
            QRAT_TRACE_BLE_FROM_STACK(lit,j,i+1-j,"universal pure");
          } else {
            if (l) { QRAT_TRACE_RATE_FROM_STACK (j,i-j,"univ pure subs"); }
          }
        }
      }
    }
  }

  if (!rm) final_rm = 1;
				// eliminate a pure literal
  if (trivial ) {
    if (!taut) {
      if ((j+abs(i-num_lits)) > 1) {
        qrat_lit = elim_lit;
        if ((final_rm || !rm)) 
          QRAT_TRACE_RATE_FROM_STACK(j,i-j,"trivial clause complete");
      }
    }
  }



  for (i = 0; i < num_lits; i++)
    lit2var (lits[i])->mark = 0;

  num_lits = j;

  trivclauseTime += (seconds() - start);
  return trivial;


}

static int trivial_clause () {
  return trivial_clause_ (0);
}



static void assign (int lit) {
  Var * v;
  assert (!deref (lit));
  assert (top_of_trail < trail + num_vars);
  *top_of_trail++ = lit;
  v = lit2var (lit);
  v->fixed = lit;
  LOG ("assign %d", lit);
  if (v->tag != FREE) return;
  fixed++;
  tag_var (v, FIXED);
  assert (remaining > 0);
  remaining--;
  LOG ("fixed %d remaining %d", lit, remaining);
}

static int isfree (int lit) {
  return lit2var (lit)->tag == FREE;
}

static void zombie (int lit) {
  assert (!lit2occ (lit)->count);
  assert (!lit2occ (-lit)->count);
  if (substituting) return;
  if (abs (lit) == elimidx) return;
  if (!isfree (lit)) return;
  if (deref (lit)) return;
  zombies++;
  tag_lit (lit, ZOMBIE);
  assert (remaining > 0);
  remaining--;
  LOG ("new zombie %d remaining %d", lit, remaining);
}

static void unet (int lit) {
  double start = seconds();
  assert (existential (lit));
  assert (!lit2occ (-lit)->count);
  if (substituting) return;
  if (abs (lit) == elimidx) return;
  if (!isfree (lit)) return;
  if (deref (lit)) return;
  unets++;
  tag_lit (lit, UNET);
  assert (remaining > 0);
  remaining--;
  LOG ("existential pure literal %d remaining %d", lit, remaining);
  assign (lit);
  if (qrat_file) {
    int tmp = lits[0];
    int tmp_num_lits = num_lits; 
    num_lits = 1;
    lits[0] = lit;
    if (!lookup_clause ()) {
      QRAT_TRACE_RATA_FROM_STACK0("existential pure");
    }
    lits[0] = tmp;
    num_lits = tmp_num_lits;
  }
  pureTime += (seconds() - start);
}

static void unate (int lit) {
  double start = seconds();
  assert (universal (lit));
  assert (!lit2occ (-lit)->count);
  assert (abs (lit) != elimidx);
  if (substituting) return;
  if (!isfree (lit)) return;
  if (deref (lit)) return;
  unates++;
  tag_lit (lit, UNATE);
  assert (remaining > 0);
  remaining--;
  LOG ("universal pure literal %d remaining %d", lit, remaining);
  assign (-lit);
  pureTime += (seconds() - start);
}

static void check_schedule (void) {
#ifndef NDEBUG
#if 0
#warning "expensive schedule checking code enabled"
  int ppos, cpos, parent, child, i;
  Var * pvar, * cvar;
  for (ppos = 0; ppos < size_schedule; ppos++) {
    parent = schedule[ppos];
    pvar = lit2var (parent);
    assert (ppos == pvar->pos);
    for (i = 0; i <= 1; i++) {
      cpos = 2*ppos + 1 + i;
      if (cpos >= size_schedule) continue;
      child = schedule[cpos];
      cvar = lit2var (child);
      assert (cvar->pos == cpos);
      assert (pvar->score <= cvar->score);
    }
  }
#endif
#endif
}

static void up (int idx) {
  int child = idx, parent, cpos, ppos, cscore;
  Var * cvar = lit2var (child), * pvar;
  cscore = cvar->score;
  cpos = cvar->pos;
  assert (cpos >= 0);
  assert (schedule[cpos] == child);
  while (cpos > 0) {
    ppos = (cpos - 1)/2;
    parent = schedule[ppos];
    pvar = lit2var (parent);
    assert (pvar->pos == ppos);
    if (pvar->score <= cscore) break;
    schedule[cpos] = parent;
    pvar->pos = cpos;
    LOG ("down %d with score %d to %d from %d",
         parent, pvar->score, cpos, ppos);
    cpos = ppos;
  }
  LOG ("up %d with score %d to %d from %d", idx, cscore, cpos, cvar->pos);
  schedule[cpos] = idx;
  cvar->pos = cpos;
  check_schedule ();
}

static void clause_stack_push () {
  int * top;  
  int i; 


  if (clause_stack_top == clause_stack_size) {
    RSZ (clause_stack, clause_stack_size, 2 * clause_stack_size);
    clause_stack_size = clause_stack_size * 2;
  }

  NEWN (clause_stack[clause_stack_top], num_lits+1);
  top = clause_stack[clause_stack_top++];

  top [0] = num_lits;


  for (i=0; i<num_lits; i++) {
    top[i+1] = lits[i];
  }

}

static void down (int idx) {
  int parent = idx, child, right, ppos, cpos, pscore;
  Var * pvar = lit2var (parent), * cvar, * rvar;
  pscore = pvar->score;
  ppos = pvar->pos;
  assert (0 <= ppos && ppos < size_schedule);
  assert (schedule[ppos] == parent);
  for (;;) {
    cpos = 2*ppos + 1;
    if (cpos >= size_schedule) break;
    child = schedule[cpos];
    cvar = lit2var (child);
    if (cpos + 1 < size_schedule) {
      right = schedule[cpos + 1];
      rvar = lit2var (right);
      if (cvar->score > rvar->score)
	cpos++, child = right, cvar = rvar;
    }
    if (cvar->score >= pscore) break;
    assert (cvar->pos == cpos);
    schedule[ppos] = child;
    cvar->pos = ppos;
    LOG ("up %d with score %d to %d from %d", child, cvar->score, ppos, cpos);
    ppos = cpos;
  }
  LOG ("down %d with score %d to %d from %d", idx, pscore, ppos, pvar->pos);
  schedule[ppos] = idx;
  pvar->pos = ppos;
  check_schedule ();
}

static void push_schedule (int idx) {
  Var * v = lit2var (idx);
  assert (v->pos < 0);
  assert (size_schedule < num_vars);
  schedule[v->pos = size_schedule++] = idx;
  LOG ("push %d", idx);
  up (idx);
  pushed_vars++;
}

static void update_score (int idx) {
  Var * v = lit2var (idx);
  int old_score = v->score;
  int pos = v->occs[0].count;
  int neg = v->occs[1].count;
  int new_score = pos + neg;
  assert (idx > 0);
  v->score = new_score;
  if (new_score < old_score)
    LOG ("score of %d decreased to %d", idx, new_score);
  if (new_score > old_score)
    LOG ("score of %d increased to %d", idx, new_score);
  if (v->pos < 0) {
     if (deref (idx)) return;
     if (elimidx != idx) push_schedule (idx);
  }
  if (new_score < old_score) {
    if (!empty_clause) {
      if (pos && !neg) {
	if (existential (idx)) unet (idx); else unate (idx);
      } else if (neg && !pos) {
	if (existential (idx)) unet (-idx); else unate (-idx);
      }
    } 
    if (v->pos >= 0) up (idx);
  }
  if (new_score > old_score && v->pos >= 0) down (idx);
}

static void add_node (Clause * clause, Node * node, int lit) {
  Occ * occ;
  assert (clause->nodes <= node && node < clause->nodes + clause->size);
  node->clause = clause;
  node->lit = lit;
  node->next = NULL;
  occ = lit2occ (lit);
  node->prev = occ->last;
  if (occ->last) occ->last->next = node;
  else occ->first = node;
  occ->last = node;
  occ->count++;
  LOG ("number of occurrences of %d increased to %d", lit, occ->count);
  update_score (abs (lit));
}

static int enqueued (Clause * clause) {
  assert (!clause->head == !clause->tail);
  return clause->head != 0;
}

static void check_queue (void) {
#if 0
#ifndef NDEBUG
#warning "expensive queue checking code enabled"
  Clause * head, * tail, * prev, * clause;
  int count;
  if (!queue) { assert (!nqueue); return; }
  clause = head = queue;
  tail = head->head;
  prev = tail;
  count = 0;
  do {
    count++;
    assert (clause->head == prev);
    assert (prev->tail == clause);
    prev = clause;
    clause = clause->tail;
  } while (clause != head);
  assert (count == nqueue);
#endif
#endif
}

static void enqueue (Clause * clause) {
  Clause * head, * tail;
  enqueued_clauses++;
  assert (!enqueued (clause));
  assert (!clause->head && !clause->tail);
  if (queue) {
    head = queue;
    tail = head->head;
    tail->tail = head->head = clause;
    clause->tail = head;
    clause->head = tail;
  } else queue = clause->head = clause->tail = clause;
  nqueue++;
  LOGCLAUSE (clause, "enqueued clause");
  assert (enqueued (clause));
  check_queue ();
}

static Sig lit2sig (int lit) {
  return 1ull << ((100623947llu * (Sig) abs (lit)) & 63llu);
}


static int least_occuring_lit_without (int min, int offset) {
  int lit, tmp, i, best = INT_MAX, blit = 0;

  assert(num_lits > 0);

  for (i=0; i < num_lits; i++) {
    if ((i >= min) && (i < min+offset)) continue;
    lit = lits[i];
    tmp = lit2occ (lit)->count;
    if (best <= tmp) continue;
    blit = lit;
    best = tmp;

  }

  LOG("found best %d",best);

  return blit;
}

static int least_occuring_lit () {
  int lit, tmp, i, best = INT_MAX, blit = 0;

  assert(num_lits > 0);

  for (i=0; i < num_lits; i++) {
    lit = lits[i];
    tmp = lit2occ (lit)->count;
    if (best <= tmp) continue;
    blit = lit;
    best = tmp;

  }

  LOG("found best %d",best);

  return blit;
}


static int least_occurring_idx (Clause * clause) {
  int best = INT_MAX, tmp, start = 0, lit;
  Node * p;
  assert (clause->size > 0);
  for (p = clause->nodes; (lit = p->lit); p++) {
    tmp = lit2occ (lit)->count + lit2occ (-lit)->count;
    if (best <= tmp) continue;
    start = abs (lit);
    best = tmp;
  }
  assert (start);
  assert (best < INT_MAX);
  LOG ("variable %d has shortest occurrence list of length %d", start, best);
  assert (best >= 1);
  return start;
}

static void watch_clause (Clause * clause) {
  int watched, lit;
  Anchor * anchor;
  Node * p;
  Sig sig;
  assert (clause->size > 1);
  watched = least_occurring_idx (clause);
  anchor = anchors + abs (watched);
  LOG ("watching %d", abs (watched));
  clause->watch.idx = abs (watched);
  if (anchor->last) {
    assert (anchor->first);
    assert (anchor->last->watch.idx == abs (watched));
    anchor->last->watch.next = clause;
  } else {
    assert (!anchor->first);
    anchor->first = clause;
  }
  clause->watch.prev = anchor->last;
  anchor->last = clause;
  anchor->count++;
  assert (anchor->count >= 0);
  sig = 0llu;
  for (p = clause->nodes; (lit = p->lit); p++)
    if (abs (lit) != watched) sig |= lit2sig (lit);
  LOG ("forward sig  %016llx without %d", sig, watched);
  fwsigs [ watched ] |= sig;
}

static int forward_subsumed_by_clause (Clause * clause, Sig sig) {
  Node * p;
  int lit;
  Var * v;

  LOGCLAUSE(clause,"checking for forward subsumption");

  if (num_lits < clause->size) return 0;
  fw.sig1.lookups++;
  if (clause->sig & ~sig) { fw.sig1.hits++; return 0; }
  for (p = clause->nodes; (lit = p->lit); p++) {
    v = lit2var (lit);
    if (v->mark != lit) return 0;
  }
  LOGCLAUSE (clause, "clause is forward subsumed");
  return 1;
}

static void check_all_unmarked (void) {
/*
#warning "expensive checking that all 'mark' flags are clear enabled"
  int idx;
  for (idx = 1; idx <= num_vars; idx++)
    assert (!vars[idx].mark);
*/}

static void mark_lit (int lit) {
  Var * v = lit2var (lit);
  assert (!v->mark);
  v->mark = lit;
}

static void submark_lit (int lit) {
  Var * v = lit2var (lit);
  assert (!v->submark);
  v->submark = lit;
}

static void unsubmark_lit (int lit) {
  Var * v = lit2var (lit);
  assert (v->submark == lit);
  v->submark = 0;
}

static void mark_lits (void) {
  int i;
  check_all_unmarked ();
  for (i = 0; i < num_lits; i++) {
    mark_lit (lits[i]);
  }
}

static void unmark_lit (int lit) {
  Var * v = lit2var (lit);
  v->mark = 0;
}


static void unmark2_lits (void) {
  int i;
  Var * v; 
  for (i = 0; i < num_lits; i++) {
    v = lit2var (lits[i]);
    v->mark3 = 0;
    v->mark2 = 0;
  }
}

static void unmark_lits (void) {
  int i;
  for (i = 0; i < num_lits; i++)
    unmark_lit (lits[i]);
  check_all_unmarked ();
}

static void mark_clause (Clause * clause) {
  Node * p;
  int lit;
  check_all_unmarked ();
  for (p = clause->nodes; (lit = p->lit); p++)
    mark_lit (lit);
}

static void unmark_clause (Clause * clause) {
  Node * p;
  int lit;
  for (p = clause->nodes; (lit = p->lit); p++)
    unmark_lit (lit);
  check_all_unmarked ();
}

static Sig sig_lits_without (int min, int offset, int *st, int size) {
  Sig res = 0ull;
  int i, lit;
  for (i = 0; i < size; i++) {
    lit = st[i];
    res |= lit2sig (lit);
  }
  return res;
}

static Sig sig_lits2 (int * st, int size) {
  Sig res = 0ull;
  int i, lit;
  for (i = 0; i < size; i++) {
    lit = st[i];
    res |= lit2sig (lit);
  }
  return res;
}

static Sig sig_lits (void) {
  Sig res = 0ull;
  int i, lit;
  for (i = 0; i < num_lits; i++) {
    lit = lits[i];
    res |= lit2sig (lit);
  }
  return res;
}


static int forward_subsumed (void) {
  int i, res, lit;
  double start = seconds(); 

  Anchor * anchor;
  Clause * p;
  Sig sig;
  res = 0;
  mark_lits ();
  sig = sig_lits ();
  for (i = 0; !res && i < num_lits; i++) {
    lit = lits[i];
    fw.sig2.lookups++;
    if (!(fwsigs [ abs (lit) ] & sig)) { fw.sig2.hits++; continue; }
    anchor = anchors + abs (lit);
    if (anchor->count > fwmaxoccs) continue;
    for (p = anchor->first; p; p = p->watch.next)
      if ((res = forward_subsumed_by_clause (p, sig))) break;
  }
  unmark_lits ();
  if (res) {
#ifndef NLOG
    if (loglevel) {
      fputs (LOGPREFIX, stdout);
      fputs ("forward subsumed clause", stdout);
      for (i = 0; i < num_lits; i++) printf (" %d", lits[i]);
      fputc ('\n', stdout);
      fflush (stdout);
      LOGCLAUSE (p, "forward subsuming clause");
    }
#endif
    if (!expanding && !substituting2) 
      if (!lookup_clause()) QRAT_TRACE_RATE_FROM_STACK0("forward subsumed");
    forward_subsumed_clauses++;
    subsumed_clauses++;
    num_lits = 0;
  }

  subsTime += (seconds() - start);
  return res;
}

static int forward_strengthened_by_clause (Clause * clause, Sig sig) {
  int lit, tmp, res;

  Node * p;
  Var * v;
  assert (num_lits <= fwmax2size);
  if (clause->size > fwmax1size) return 0;
  if (num_lits < clause->size) return 0;
  fw.sig1.lookups++;
  if (clause->sig & ~sig) { fw.sig1.hits++; return 0; }
  res = 0;
  for (p = clause->nodes; (lit = p->lit); p++) {
    v = lit2var (lit);
    tmp = v->mark;
    if (tmp == lit) continue;
    if (tmp != -lit) return 0;
    if (res) return 0;
    res = -lit;
  }

  return res;
}

static Clause * lookup_without_lit (int lit) {
  int pos;
  Clause * c;


  for (pos = 0; pos < num_lits; pos++) {
    if (lits[pos] == lit) break;
  }


  assert (pos <= num_lits);


  if (pos == num_lits) {
    return lookup_clause ();
  }

  num_lits--;
  lits[pos] = lits[num_lits];
  lits[num_lits] = lit;


  c = lookup_clause ();
  num_lits++;
  return c;


}

static void forward_strengthen (void) {
  int i, j, k, res, lit, pivot, other;
#ifndef NDEBUG
  int found;
#endif
  double start = seconds();
  Anchor * anchor;
  Clause * p;
  Sig sig;
  Var * v;
  if (num_lits > fwmax2size) return;
  sig = sig_lits ();
  mark_lits ();
  res = 0;
RESTART:
  for (i = 0; !res && i < num_lits; i++) {
    lit = lits[i];
    fw.sig2.lookups++;
    if (!(fwsigs [ abs (lit) ] & sig)) { fw.sig2.hits++; continue; }
    anchor = anchors + abs (lit);
    if (anchor->count > fwmaxoccs) continue;
    for (p = anchor->first; p; p = p->watch.next) {
      pivot = forward_strengthened_by_clause (p, sig);
      if (!pivot) continue;
#ifndef NLOG
      if (loglevel) {
	fputs (LOGPREFIX, stdout);
	printf ("forward strengthening by removing %d from clause", pivot);
	for (j = 0; j < num_lits; j++) printf (" %d", lits[j]);
	fputc ('\n', stdout);
	fflush (stdout);
	LOGCLAUSE (p, "used clause for forward strengthening");
      }
#endif
      v = lit2var (pivot);
      assert (v->mark == pivot);
      v->mark = 0;
      k = 0;
      assert (!(found = 0));
      if (!lookup_without_lit (pivot)) {
        QRAT_TRACE_RATA_FROM_STACK_WITHOUT_LIT(pivot,"forward strengthening");
      }
      if (!expanding) QRAT_TRACE_RATE_FROM_STACK0("forward strengthening");
      for (j = 0; j < num_lits; j++) {
	other = lits[j];
	if (other != pivot) lits[k++] = other;
	else assert ((found = 1));
      }
      assert (k + 1 == num_lits);
      assert (found);
      num_lits--;
      sig = sig_lits ();
      forward_strengthened_clauses++;
      strengthened_clauses++;
      goto RESTART;
    }
  }
  unmark_lits ();
  strengthTime += (seconds() - start); 
}

static void add_clause (void) {
  Clause * clause;
  size_t bytes;
  int i;
  Var * v;

  if (!substituting2) {
    LOG("trying forward subsumption");
    if (forward_subsumed ()) {
      return;
    }
    LOG("trying strengthening ");
    forward_strengthen ();
  }


  forall_reduce_clause ();
 
  bytes = bytes_clause (num_lits);
  clause = malloc (bytes);
  if (!clause) die ("out of memory");
  assert (clause);
  memset (clause, 0, bytes);
  assert (!clause->nodes[num_lits].lit);
  INC (bytes);
  clause->count = 1;
  clause->size = num_lits;
  clause->prev = last_clause;
  clause->sig = sig_lits ();;
  LOG ("signature %016llx", clause->sig);
  if (last_clause) last_clause->next = clause;
  else first_clause = clause;
  last_clause = clause;
  for (i = 0; i < num_lits; i++)
    add_node (clause, clause->nodes + i, lits[i]);
  num_lits = 0;
  LOGCLAUSE (clause, "adding length %d clause", clause->size);
  if (!clause->size) {
    if (empty_clause) {
 	msg ("found another empty clause");
     }
    else {
      msg ("found empty clause");
      LOG ("found empty clause");
      empty_clause = clause;
    }
  } else if (clause->size == 1) {
    int lit = clause->nodes[0].lit;
    v = lit2var (lit);
    if (v->tag == FREE) { 
      LOG ("unit %d", lit);
      fixed++;
      tag_var (v, UNIT);
      assert (remaining > 0);
      remaining--;
      LOG ("fixed %d remaining %d", lit, remaining);
      units++;
      LOG("detected unit clause");
      assign (lit);
    }
  } else {
    enqueue (clause);
    watch_clause (clause);
  }
  added_clauses++;
  if (clause->size == 2) {
    added_binary_clauses++;
  }
  num_clauses++;
  LOG("adding clause done");
}

static void delete_node (Node * node) {
  Occ * occ = lit2occ (node->lit);
  assert (occ-> count > 0);
  if (node->prev) {
    assert (node->prev->next == node);
    node->prev->next = node->next;
  } else {
    assert (occ->first == node);
    occ->first = node->next;
  }
  if (node->next) {
    assert (node->next->prev == node);
    node->next->prev = node->prev;
  } else {
    assert (occ->last == node);
    occ->last = node->prev;
  }
  occ->count--;
  LOG ("number of occurrences of %d decreased to %d", node->lit, occ->count);
  update_score (abs (node->lit));
}

static void dequeue (Clause * clause) {
  assert (nqueue > 0);
  assert (enqueued (clause));
  if (clause->head == clause) {
    assert (clause->tail == clause);
    assert (queue == clause);
    queue = 0;
  } else {
    clause->head->tail = clause->tail;
    clause->tail->head = clause->head;
    if (queue == clause) queue = clause->tail;
  }
  clause->head = clause->tail = 0;
  LOGCLAUSE (clause, "dequeued clause");
  assert (!enqueued (clause));
  nqueue--;
}

static void unwatch_clause (Clause * clause) {
  Anchor * anchor;
  assert (clause->size > 1);
  anchor = anchors + abs (clause->watch.idx);
  if (clause->watch.prev) {
    clause->watch.prev->watch.next = clause->watch.next;
  } else {
    assert (anchor->first == clause);
    anchor->first = clause->watch.next;
  }
  if (clause->watch.next) {
    clause->watch.next->watch.prev = clause->watch.prev;
  } else {
    assert (anchor->last == clause);
    anchor->last = clause->watch.prev;
  }
  LOG ("unwatched %d", clause->watch.idx);
  assert (anchor->count > 0);
  anchor->count--;
}

static void delete_clause (Clause * clause) {
  size_t bytes;
  int i;

  assert (num_clauses > 0);
  LOGCLAUSE (clause, "deleting length %d clause", clause->size);
  bytes = bytes_clause (clause->size);
  if (clause->prev) {
    assert (clause->prev->next == clause);
    clause->prev->next = clause->next;
  } else {
    assert (first_clause == clause);
    first_clause = clause->next;
  }
  if (clause->next) {
    assert (clause->next->prev == clause);
    clause->next->prev = clause->prev;
  } else {
    assert (last_clause == clause);
    last_clause = clause->prev;
  }
  for (i = 0; i < clause->size; i++)
    delete_node (clause->nodes + i);
  if (clause->size > 1) unwatch_clause (clause);
  if (enqueued (clause)) dequeue (clause);
  DEC (bytes);
  free (clause);
  num_clauses--;
}

static void enlarge_lits (void) {
  int new_size_lits = size_lits ? 2*size_lits : 1;
  RSZ (lits, size_lits, new_size_lits);
  size_lits = new_size_lits;
}

static void push_literal (int lit) {
  assert (abs (lit) <= num_vars);
  if (size_lits == num_lits) enlarge_lits ();
  lits[num_lits++] = lit;
}

static void log_declared_scopes (void) {
  int count, o, c;
  Scope * p;
  Var * q;
  if (notclean) clean_line ();
  fputs ("c [bloqqer] ", stdout);
  for (p = outer_most_scope; p; p = p->inner) {
    if (p == outer_most_scope) assert (p->type > 0), o = '(', c = ')';
    else if (p->type < 0) o = '[', c = ']';
    else o = '<', c = '>';
    fputc (o, stdout);
    count = 0;
    for (q = p->first; q; q = q->next)
      count++;
    printf ("%d", count);
    fputc (c, stdout);
  }
  fputc ('\n', stdout);
  fflush (stdout);
}

static void init_implicit_scope (void) {
  Var * v;
  int idx;
  int count = 0; 
  Var * p;

  assert (!implicit_vars);
  implicit_vars = num_vars - universal_vars - existential_vars;
  existential_vars += implicit_vars;
  assert (implicit_vars >= 0);
  msg ("%d universal, %d existential variables (%d implicit)",
       universal_vars, existential_vars, implicit_vars);
  if (implicit_vars > 0) {

    if (!outer_most_scope) add_outer_most_scope ();
    for (v = vars + 1; v <= vars + num_vars; v++)
      if (!v->scope) {
        idx = v - vars;
        LOG ("implicitly existentially quantified variable %d", idx);
        add_var (idx, outer_most_scope);
      }
  }

  for (p = outer_most_scope->first; p; p = p->next) {
    count++;
  }

  if (count == 0) assigned_scope = 1; 
  else assigned_scope = 0;


  if (verbose) log_declared_scopes ();
}

static void init_variables (int start) {
  int i;
  assert (0 < start && start <= num_vars);
  for (i = start; i <= num_vars; i++) {
    Var * v = vars + i;
    v->pos = -1;
    v->mark = 0;
    v->mark2 = v->mark3 = v->mark4 = 0;
    v->mapped = ++mapped;
    assert (mapped == i);
  }
  assert (mapped == num_vars);
}

static int null_occurrences (int lit) {
  Var * v = lit2var (lit);
  if (v->occs[0].count) return 0;
  if (v->occs[1].count) return 0;
  return 1;
}

static void log_pruned_scopes (void) {
  int count, prev, this;
  Scope * p;
  Var * q;
  if (notclean) clean_line ();
  fputs ("c [bloqqer] ", stdout);
  count = prev = 0;
  for (p = outer_most_scope; p; p = p->inner) {
    this = 0;
    for (q = p->first; q; q = q->next)
      if (q->tag == FREE) this++;
    if (!this) continue;
    if (prev != p->type) {
      if (prev) {
	fputc ((prev < 0) ? '[' : '<', stdout);
	printf ("%d", count);
	fputc ((prev < 0) ? ']' : '>', stdout);
	count = 0;
      } else assert (!count);
      prev = p->type;
    }
    count += this;
  }
  fputc ((prev < 0) ? '[' : '<', stdout);
  printf ("%d", count);
  fputc ((prev < 0) ? ']' : '>', stdout);
  fputc ('\n', stdout);
  fflush (stdout);
}

static int parse_short_opt (const char * arg) {
  int ch = arg[0], val;
  Opt * p;
  if (!ch || arg[1]) return 0;
  for (p = opts; p->inc != ch && p->name; p++)
    ;
  if (!p->name) return 0;
  val = *p->valptr + 1;
  if (val <= p->high) *p->valptr = val;
  else wrn ("ignoring '-%c' (maximum value %d reached)", p->inc, p->high);
  return 1;
}

static void force_bound (void) {
  fwmaxoccs = fwmax1size = fwmax2size = bwmaxoccs = bound;
  bwmax1size = bwmax2size = blkmax1occs = blkmax2occs = bound;
  blkmax1size = blkmax2size = elimoccs = elimsize = bound;
}

static void reinit_opt (const char * name) {
  Opt * p;
  for (p = opts; p->name; p++)
    if (!strcmp (name, p->name))
      break;
  assert (p->name);
  *p->valptr = p->def;
}

static void force_no_bound (void) {
  reinit_opt ("fwmaxoccs");
  reinit_opt ("fwmax1size");
  reinit_opt ("fwmax2size");
  reinit_opt ("bwmaxoccs");
  reinit_opt ("bwmax1size");
  reinit_opt ("bwmax2size");
  reinit_opt ("blkmax1occs");
  reinit_opt ("blkmax2occs");
  reinit_opt ("blkmax1size");
  reinit_opt ("blkmax2size");
  reinit_opt ("elimoccs");
  reinit_opt ("elimsize");
}

static int parse_long_opt (const char * arg) {
  const char * q, * valstr;
  int len, oldval, newval;
  Opt * p;
  StrOpt * s;
  if (!*arg) return 0;
  q = strchr (arg, '=');
  len = q ? q - arg : strlen (arg);


  for (s = str_opts; s->name; s++)
    if (strlen (s->name) == len && !strncmp (arg, s->name, len))
      break;
  if (s->name) {
    assert (*q == '=');
    qrat_trace = q+1; 
    return 1;
  }

  for (p = opts; p->name; p++)
    if (strlen (p->name) == len && !strncmp (arg, p->name, len))
      break;
  if (!p->name) return 0;
  oldval = *p->valptr;
  if (q) {
      assert (*q == '=');
      valstr = ++q;
      if (*q == '-') q++;
      if (!isdigit (*q)) return 0;
      while (isdigit (*q)) q++;
      if (*q) return 0;
      newval = atoi (valstr);
    }
  else if (arg[len]) return 0;
  else newval = oldval + 1;
  if (newval < p->low) {
    newval = p->low;
    wrn ("capping '--%s' with minimum value %d", arg, p->low);
  }
  if (newval > p->high) {
    newval = p->high;
    wrn ("capping '--%s' with maximum value %d", arg, p->high);
  }
  *p->valptr = newval;
  if (!strcmp (p->name, "bound")) {
    assert (p->low == -1);
    if (newval == -1) force_no_bound ();
    else force_bound ();
  }
  return 1;
}

static int parse_no_long_opt (const char * arg) {
  Opt * p;
  for (p = opts; p->name; p++)
    if (!strcmp (arg, p->name)) break;
  if (!p->name) return 0;
  *p->valptr = p->low;
  if (!strcmp (p->name, "bound")) force_no_bound ();
  return 1;
}

static int parse_opt (const char * arg) {
  int res;
  if (!strcmp (arg, "-n")) output = 0, res = 1;
  else if (arg[0] == '-' && arg[1] != '-') res = parse_short_opt (arg + 1);
  else if (!strncmp (arg, "--no-", 5)) res = parse_no_long_opt (arg + 5);
  else if (arg[0] == '-' && arg[1] == '-') res = parse_long_opt (arg + 2);
  else res = 0;
  return res;
}

static void embedded_opt (char * line) {
  const char * opt;
  char * p, ch;
  if (ignore) return;
  for (p = line; isspace (*p); p++)
    ;
  if (*p != '-') return;
  opt = p++;
  while (isalnum (*p) || *p == '-') p++;
  if (*p == '=') {
    p++;
    if (*p == '-') p++;
    while (isdigit (*p)) p++;
  }
  if (*p && *p != ' ' && *p != '\t' && *p != '\r') {
    ch = *p;
    *p = 0;
    wrn ("unexpected character 0x%02x after embedded option: %s", ch, opt);
    return;
  }
  *p = 0;
  if (parse_opt (opt)) {
    msg ("embedded option: %s", opt);
    embedded_options++;
  } else wrn ("invalid embedded option: %s", opt);
}

static void list_opts_values (void) {
  Opt * p;
  StrOpt * q;
  for (p = opts; p->name; p++)
    printf ("c [bloqqer] --%s=%d\n", p->name, *p->valptr);

  for (q = str_opts; q->name; q++)
    printf ("c [bloqqer] --%s=%s\n", q->name, *q->valptr);
}

static int get_scopesize (Scope * s) {

  int i = 0;
  Var * v;

  for (v = s->first; v; v = v->next) {
    i++;
  }

  return i;  

}


static const char * parse (FILE * ifile, char * iname) {
  int ch, m, n, i, j, c, q, lit, sign, started;
  double start;


  start = seconds ();
  msg ("reading %s", iname);

  lineno = 1;
  i = c = q = 0;

  assert (!universal_vars);
  assert (!existential_vars);

  szline = 128;
  assert (!line);
  NEWN (line, szline);
  nline = 0;

SKIP:
  ch = getc (ifile);
  if (ch == '\n') { lineno++; goto SKIP; }
  if (ch == ' ' || ch == '\t' || ch == '\r') goto SKIP;
  if (ch == 'c') {
    line[nline = 0] = 0;
    while ((ch = getc (ifile)) != '\n') {
      if (ch == EOF) return "end of file in comment";
      if (nline + 1 == szline) {
	RSZ (line, szline, 2*szline);
	szline *= 2;
      }
      line[nline++] = ch;
      line[nline] = 0;
    }
    embedded_opt (line);
    lineno++;
    goto SKIP;
  }
  if (ch != 'p') {
HERR:
    return "invalid or missing header";
  }
  if (verbose) {
    if (ignore) msg ("disabled parsing and ignored embedded options");
    else msg ("finished parsing %d embedded options", embedded_options);
    msg ("listing final option values:");
    list_opts_values ();
  }
  if (getc (ifile) != ' ') goto HERR;
  while ((ch = getc (ifile)) == ' ')
    ;
  if (ch != 'c') goto HERR;
  if (getc (ifile) != 'n') goto HERR;
  if (getc (ifile) != 'f') goto HERR;
  if (getc (ifile) != ' ') goto HERR;
  while ((ch = getc (ifile)) == ' ')
    ;
  if (!isdigit (ch)) goto HERR;
  m = ch - '0';
  while (isdigit (ch = getc (ifile)))
    m = 10 * m + (ch - '0');
  if (ch != ' ') goto HERR;
  while ((ch = getc (ifile)) == ' ')
    ;
  if (!isdigit (ch)) goto HERR;
  n = ch - '0';
  while (isdigit (ch = getc (ifile)))
    n = 10 * n + (ch - '0');
  while (ch != '\n')
    if (ch != ' ' && ch != '\t' && ch != '\r') goto HERR;
    else ch = getc (ifile);
  lineno++;
  msg ("found header 'p cnf %d %d'", m, n);
  remaining = num_vars = m;
  remaining_clauses_to_parse = n;
  NEWN (vars, num_vars + 1);
  if (num_vars) init_variables (1);
  NEWN (dfsi, 2*num_vars+1);
  dfsi += num_vars;
  NEWN (mindfsi, 2*num_vars+1);
  mindfsi += num_vars;
  orig_num_vars = num_vars;
  NEWN (repr, 2*num_vars+1);
  repr += num_vars;
  NEWN (subst_vals, num_vars+1);
  for (j = 0; j < num_vars+1; j++) {
    subst_vals [j] = j;
  }
  NEWN (fwsigs, num_vars + 1);
  NEWN (bwsigs, num_vars + 1);
  NEWN (anchors, num_vars + 1);
  NEWN (trail, num_vars);
  NEWN (clause_stack, num_vars);
  clause_stack_top = 0;
  clause_stack_size = num_vars;
  top_of_trail = next_on_trail = trail;
  NEWN (schedule, num_vars);
  assert (!size_schedule);
  started = 0;
NEXT:
   ch = getc (ifile);
   if (ch == '\n') { lineno++; goto NEXT; }
   if (ch == ' ' || ch == '\t' || ch == '\r') goto NEXT;
   if (ch == 'c') {
     while ((ch = getc (ifile)) != '\n')
       if (ch == EOF) return "end of file in comment";
     lineno++;
     goto NEXT;
   }
   if (ch == EOF) {
     if (!force && i < n) return "clauses missing";
     orig_clauses = i;
     if (!q && !c) init_implicit_scope ();
     goto DONE;
   }
   if (ch == '-') {
     if (q) return "negative number in prefix";
     sign = -1;
     ch = getc (ifile);
     if (ch == '0') return "'-' followed by '0'";
   } else sign = 1;
   if (ch == 'e') { 
     if (c) return "'e' after at least one clause";
     if (q) return "'0' missing after 'e'";
     q = 1;
     goto NEXT;
   }
   if (ch == 'a') { 
     if (c) return "'a' after at least one clause";
     if (q) return "'0' missing after 'a'";
     q = -1; 
     goto NEXT;
   }
   if (!isdigit (ch)) return "expected digit";
   lit = ch - '0';
   while (isdigit (ch = getc (ifile)))
     lit = 10 * lit + (ch - '0');
   if (ch != EOF && ch != ' ' && ch != '\t' && ch != '\n' && ch != '\r')
     return "expected space after literal";
   if (ch == '\n') lineno++;
   if (lit > m) return "maximum variable index exceeded";
   if (!force && !q && i == n) return "too many clauses";
   if (q) {
     if (lit) {
       if (sign < 0) return "negative literal quantified";
       if (lit2scope (lit)) {
            return "variable quantified twice";
       }
       lit *= q;
       add_quantifier (lit);
       if (q > 0) existential_vars++; else universal_vars++;
     } else q = 0;
   }
   else {
     if (!q && !c) {
       started = 1;
       init_implicit_scope ();
       start_progress ("remaining clauses to parse",
                       &remaining_clauses_to_parse);
     }
     if (lit) lit *= sign, c++; else i++, remaining_clauses_to_parse--;
     if (lit) push_literal (lit);
     else {
       if (!empty_clause && !trivial_clause_ (1)) {
	 add_clause ();
	 if (empty_clause) {
	   orig_clauses = i;
	   goto DONE;
	 }
       } else {
         num_lits = 0;
       }       
      }
   }
   goto NEXT;
DONE:
  if (started) stop_progress ();
  parseTime = seconds() - start;
  msg ("read %d literals in %.1f seconds", c, parseTime);
  if (verbose) log_pruned_scopes ();
  return 0;
}


static void partial_expansion () {
  int univ_size = get_scopesize (inner_most_scope->outer);
  int exist_size = get_scopesize (inner_most_scope);
  int total = univ_size + exist_size;
  int i, j; 
  int univ_order = inner_most_scope->outer->order;
  int copies, old_numvars;

  Var * v;
  Clause * p;
  Node * n;
  int * new_vals;
  Clause * l = last_clause;
  if (!guessnumber) return;
  LOG("doing partial expansion");

  NEWN (new_vals, total);
  srand(time(NULL));
  for (i = 0; i < guessnumber; i++) {
    for (v = inner_most_scope->outer->first; v; v = v->next) {
      v->expcopy = rand () % 2;
    }
    j = 1;
    for (v = inner_most_scope->first; v; v = v->next) {
      v->expcopy = num_vars+j;
      j++;
    }
    old_numvars = num_vars;
    copies = j;
    enlarge_vars (num_vars + j + 1);
    LOG("enlarged clauses");
  
    for (j = 1; j <= copies+1; j++) {
      add_var (old_numvars+j, inner_most_scope);
    }

    LOG("adding partially expanded clauses");
    num_lits = 0; 
    for (p = first_clause; p != l; p = p->next) {
      LOGCLAUSE(p, "checking clause for partial expansion");
      for (n = p->nodes; n->lit; n++) {
        v = lit2var(n->lit);
        if (v->scope->order >= univ_order) {
          if (v->scope->order == univ_order) {
            if ((n->lit > 0 && v->expcopy == 0) || 
                (n->lit < 0 && v->expcopy == 1)) {
              LOG("literal %d is skipped in expanded clause",n->lit);
              continue;
            }
            LOG("expanded clause is not added because of %d",n->lit);
            num_lits = 0;
            break;
          } else {
            LOG("adding replaced literal %d for %d",v->expcopy, n->lit);
            if (n->lit < 0) push_literal(-v->expcopy);
            else push_literal(v->expcopy);
          }
        } else {
          LOG("adding literal %d ",n->lit); 
          push_literal(n->lit);
        }
      }
      if (num_lits) { 
        LOG("adding clause");
        add_clause ();
        num_lits = 0; 
      }
    }
  }
  flush_vars ();
  DELN (new_vals, total);


}


static int var2lit (Var * v) { 
  assert (vars < v && v <= vars + num_vars);
  return (int)(long)(v - vars);
}

static int map_lit (int lit) {
  Var * v = lit2var (lit);
  int res = v->mapped;
  assert (res);
  if (lit < 0) res = -res;
  return res;
}

static int trail_flushed (void) {
  return next_on_trail == top_of_trail;
}

static void flush_pos (int lit) {
  Occ * occ = lit2occ (lit);
  Node * p, * next;
  Clause * unit_clause = NULL;
  Var * v = lit2var (lit);
  
  LOG ("flushing positive occurrences of %d", lit);
  for (p = occ->first; p; p = next) {
    next = p->next;
    if ((p->clause->size != 1)) {
      if (v->tag != EXPANDED) {
        qrat_lit = lit;
        QRAT_TRACE_RATE_FROM_CLAUSE(p->clause,"unit or pure"); 
      }
      delete_clause (p->clause);
    } else {
      if (v->tag != EXPANDED) unit_clause = p->clause;
    }
  }
  if (unit_clause) {
    assert (unit_clause->nodes[0].lit == lit);
    QRAT_TRACE_RATE_FROM_CLAUSE(unit_clause,"unit"); 
    delete_clause (unit_clause);
  }
  assert (!occ->count);
}


static int is_satisfied () {
  int i, lit, tmp; 

  for (i = 0; i < num_lits; i++) {
    lit = lits[i];
    LOG("sat check of %d", lit);
    tmp = deref(lit); 
    if (tmp > 0) return lit;
  }

  return 0;

}

static void flush_node (Node * node) {
  int lit = node->lit, other;
  Clause * clause = node->clause;
  Node * p;
  Var * v = lit2var (lit);
  Clause * c;
  int k; 
#ifndef NDEBUG
  int found;
#endif

  assert (!num_lits);
  assert (!(found = 0));

  LOG("flushing node %d", lit);
  for (p = clause->nodes; (other = p->lit); p++) {
    if (other == lit) { assert ((found = 1)); continue; }
    assert (num_lits < size_lits);
    lits[num_lits++] = other;
  }

  if ((c =lookup_clause ())) {	// the new clause is already there
    LOGCLAUSE(clause,"subsumed clause after removing node");
    QRAT_TRACE_RATE_FROM_CLAUSE(clause,"removed one literal from ");
    delete_clause (clause);
    num_lits = 0;
    return;
  }


  if (v->tag != EXPANDED) {
    if (v->scope->type > 0) {
      if ((num_lits != 1) || 
          ((num_lits == 1) && ((lit2var(lits[0])->tag == FREE) 
             || (lit2var(lits[0])->fixed != lits[0]))))
           {
             QRAT_TRACE_RATA_FROM_STACK0("reduction from unit"); 
           } else {
             if (num_lits == 1) {
             	qrat_lit = lits[0];
 	     }
	   }
      if (!qrat_lit) qrat_lit = lit;
      QRAT_TRACE_RATE_FROM_CLAUSE(clause,"unit propagation");

      if (is_sat () && lookup_clause()) {
        qrat_lit = is_satisfied ();
        QRAT_TRACE_RATE_FROM_STACK0("rm satisfied clause");
      }
    } else {
      k = is_satisfied ();
      if (k) {
        qrat_lit = k;
        push_literal (lit);
        QRAT_TRACE_RATE_FROM_STACK0("univ pure elim in satisfied clause");
        num_lits = 0;
        delete_clause (clause);
        return;
      }
      if (!lookup_without_lit (lit)) {
        QRAT_TRACE_BLE_FROM_CLAUSE(lit,clause,"universal pure in flush node");
      } else {
        QRAT_TRACE_RATE_FROM_CLAUSE(clause, "univ pure subs in fush node");
      }

    }
  } else {
    LOGCLAUSE(clause, "node is removed due to expansion");
  } 

  assert (found);
  if (trivial_clause ()) {
     num_lits = 0;
  } else {
    add_clause ();
  }
  delete_clause (clause);
  do_qrat = 1;
}

static void flush_neg (int lit) {
  Occ * occ = lit2occ (-lit);
  Node * p, * next;
  LOG ("flushing negative occurrences of %d", lit);
  for (p = occ->first; p; p = next) {
    next = p->next;
    LOGCLAUSE(p->clause, "next clause");
    flush_node (p);
  }
  LOG ("flushing negative occurrences of %d done", lit);
  assert (!occ->count);
}

static void flush_lit (int lit) {

    flush_neg (lit);
    flush_pos (lit);
    assert (null_occurrences (lit));
}

static void flush_trail (void) {
  Clause * p, * next;
  int idx, lit;
  Var * v;
  int pure = 0;
  while (!empty_clause && !trail_flushed ()) {
    lit = *next_on_trail++;
    v = lit2var (lit);

    if ((qrat_file) && (v->tag == UNET)) {
      assert(!num_lits);
      push_literal (lit); 
      if (!lookup_clause ()) {
        pure = 1; 
        num_lits = 0;
      } 
    }
    flush_lit (lit);
    if (pure)  {
      pure = 0;
      push_literal(lit);
      QRAT_TRACE_RATE_FROM_STACK0("existential pure");
      num_lits = 0;
    }
  }
  if (empty_clause) {
    for (p = first_clause; p; p = next) {
      next = p->next;
      if (p == empty_clause) continue;
      QRAT_TRACE_RATE_FROM_CLAUSE(p,
             "empty clause after bcp (delete all others)");
      delete_clause (p);
      subsumed_clauses++;
    }
    for (idx = 1; idx <= num_vars; idx++) {
      v = vars + idx;
      assert (null_occurrences (idx));
      if (v->tag != FREE) continue;
      zombie (idx);
    }
    next_on_trail = top_of_trail;
  }
  assert (trail_flushed ());
}

static int pop_schedule (void) {
  int res, lpos, last;
  Var * rvar, * lvar;
  assert (size_schedule > 0);
  res = schedule[0];
  rvar = lit2var (res);
  assert (!rvar->pos);
  rvar->pos = -1;
  lpos = --size_schedule;
  if (lpos > 0) {
    last = schedule[lpos];
    lvar = lit2var (last);
    assert (lvar->pos == lpos);
    schedule[0] = last;
    lvar->pos = 0;
    down (last);
  }
  LOG ("pop %d with score %d", res, rvar->score);
  return res;
}


static int block_clause_aux (int pivot) {
  int res, lit, tmp, porder, lorder;
#ifndef NDEBUG
  int found;
#endif
  Clause * other;
  Node * p, * q;
  Occ * occ;
  Var * v;
  res = 1;
  if (partial_assignment && lit2order(pivot) == assigned_scope) return 0;
  occ = lit2occ (-pivot);
  porder = lit2scope (pivot)->order;
  for (p = occ->first; res && p; p = p->next) {
    assert (p->lit == -pivot);
    other = p->clause;
    assert (other->size >= 2);
    if (other->size > blkmax2size) { res = 0; continue; }
    assert (!(found = 0));
    LOGCLAUSE (other, "try to resolve on %d with other clause", pivot);
    for (q = other->nodes; (lit = q->lit); q++) {
      if (lit == -pivot) { assert (p == q); assert ((found = 1)); continue; }
      lorder = lit2scope (lit)->order;
      if (lorder > porder) continue;//TODO triangle dependencies?
      v = lit2var (lit);
      tmp = v->mark;
      if (tmp == -lit) break;
    }
    assert (lit || found);
    if (lit) LOG ("other clause produces trivial resolvent on %d", lit);
    else { LOG ("other clause produces non-trivial resolvent"); res = 0; }
  }
  return res;
}

static int block_clause (Clause * clause, int pivot) {
  Occ * occ;
  int res;
  if (clause->size > blkmax1size) return 0;
  occ = lit2occ (-pivot);
  if (occ->count > blkmax1occs) return 0;
  LOGCLAUSE (clause, "check whether literal %d blocks clause", pivot);
  mark_clause (clause);
  res = block_clause_aux (pivot);
  unmark_clause (clause);
  return res;
}

static void block_lit (int lit) {
  Node * p, * next, * q;
  Clause * clause;
  Occ * occ;
  double start = seconds();
  int lit2; 

  if (partial_assignment && lit2order(lit) == assigned_scope) return;
  if (!bce && !ble) return;
  if (existential (lit) && !bce) return;
  if (!existential (lit) && !ble) return;
  occ = lit2occ (lit);
  if (occ->count > blkmax2occs) return;
  LOG ("CHECKING %d as blocking literal", lit);
  for (p = occ->first; trail_flushed () && p; p = next) {
    next = p->next;
    clause = p->clause;
    if (!block_clause (clause, lit)) continue;
    LOGCLAUSE (clause, "literal %d blocks clause", lit);
    if (!partial_assignment || !p->blocked) {

 	if (universal (lit)) {
          for (q = clause->nodes; (lit2 = q->lit); q++) {
	    if (lit != lit2) push_literal (lit2);
	  }
          if (!lookup_clause ())  {
            QRAT_TRACE_BLE_FROM_CLAUSE(lit,clause,"blocked literal");
	  } else {
            qrat_lit = 0;
            QRAT_TRACE_RATE_FROM_CLAUSE(clause,"blocked literal");
	  }
          LOGCLAUSE (clause, "blocked literal %d in clause", lit);
          add_clause ();
	  blocked_lits++;
	} else {
          qrat_lit = lit;
          QRAT_TRACE_RATE_FROM_CLAUSE(clause,"blocked clause");
	  blocked_clauses++;
	}
	delete_clause (clause);

    } else {
	outermost_blocked++;
	p->blocked = 1;
	LOGCLAUSE(clause,"not blocked because pivot is in outermost scope and part. assignment is demanded");
    }
  }
  bceTime += (seconds() - start);
}

static int try_to_resolve_away (int limit) {
  int elimidx_order, lit_order, lit, mini_scope, count, nontriv,  res;
  int clash = 0, nonstrictve = 0;
  double start;
  Node * p, * q, * r;
  Occ * pocc, * nocc;
  Clause * c, * d;
  int cpos, dpos;
  assert (trail_flushed ());
  assert (existential (elimidx));
  assert (!deref (elimidx));
  assert (limit < INT_MAX-1);
  if (!ve) return 0;
  start = seconds();
  elimidx_order = lit2scope (elimidx)->order;
  nontriv = count = 0;
  pocc = lit2occ (elimidx);
  nocc = lit2occ (-elimidx);
  for (p = pocc->first;
       trail_flushed () && nontriv <= limit && p;
       p = p->next) {
    c = p->clause;
    if (c->size > elimsize) { nontriv = INT_MAX-1; continue; }
    mark_clause (c);
    mini_scope = 1;
    for (q = nocc->first;
         trail_flushed () && nontriv <= limit && q;
	 q = q->next) {
      count++;
      d = q->clause;
      if (d->size > elimsize) { nontriv = INT_MAX-1; continue; }
      LOGCLAUSE (c, "%d:%d/%d elimination %d clause",
                count, nontriv + 1, limit, elimidx);
      LOGCLAUSE (d, "%d:%d/%d elimination %d clause",
		 count, nontriv + 1, limit, -elimidx);
      clash =  0;
      for (r = d->nodes; (lit = r->lit); r++) {
	if (lit == -elimidx) { continue; }
	lit_order = lit2scope (lit)->order;
	if (lit_order > elimidx_order) { 
	  if (mini_scope) 
	    LOG ("literal %d in scope %d prevents mini-scoping", 
	         lit, lit_order);
	  mini_scope = 0; 
	} else if (clash) continue;
	else if (lit2var (lit)->mark == -lit) clash = lit;
      }
      // COVER (clash && !mini_scope);
      if (clash) {
	LOG ("literal %d in scope %d makes resolvent trivial",
	     clash, lit2order (clash));
	if (!mini_scope) {
	  if (strict) {
	    LOG ("but strict variable elimination prevents resolution");
	    nontriv = INT_MAX;
	  } else {
	    LOG ("non-strict mini-scoping applied");
	    nonstrictve = 1;
	  }
	}
      } else if (mini_scope) {
	LOG ("non-trivial resolvent can be mini-scoped");
	nontriv++;
	if (c->size == 2 && d->size == 2) {
	  cpos = abs (c->nodes[1].lit) == elimidx;
	  dpos = abs (d->nodes[1].lit) == elimidx;
	  lit = c->nodes[!cpos].lit;
	  if (d->nodes[!dpos].lit == lit) {
	    LOG ("unit %d during temptative resolution", lit);
            QRAT_TRACE_RATA_UNIT(lit,"unit by resovling binary clauses");
	    units++;
            LOG("unit in expansion");
	    assign (lit);
	  }
	}
      } else {
        assert (!mini_scope);
	assert (!clash || strict);
	LOG ("non-trivial resolvent can NOT be mini-scoped");
	nontriv = INT_MAX;
      }
    }
    unmark_clause (c);
  }
  if (trail_flushed ()) {
    res = (nontriv <= limit);
#ifndef NLOG
    if (nontriv <= limit) 
      LOG ("resolving away %d will generate only %d clauses not exceeding %d",
	   elimidx, nontriv, limit);
    else if (nontriv < INT_MAX-1)
      LOG ("resolving away %d would generate at least one additional clause",
	   elimidx);
    else if (nontriv == INT_MAX-1) {
      LOG ("resolving away %d involves too large clauses", elimidx);
    } else {
      assert (nontriv == INT_MAX);
      LOG ("mini-scoping and resolving away %d is impossible", elimidx);
    }
#endif
  } else {
    LOG ("unit resolvent stops temptatively resolving away %d", elimidx);
    res = 0;
  }
  if (res && nonstrictve) nonstrictves++;
  veTime += (seconds() - start);
  return res;
}

static void resolve_away (int idx) {
  Node * p, * q, * r, * next;
  Clause * c, * d;
  int lit;

  assert (elimidx > 0);
  assert (!deref (elimidx));
  assert (trail_flushed ());
  LOG ("RESOLVING away %d", elimidx);
  for (p = lit2occ (elimidx)->first; p; p = p->next) {
    c = p->clause;
    for (q = lit2occ (-elimidx)->first; q; q = q->next) {
      d = q->clause;
      assert (!num_lits);
      LOGCLAUSE (c, "%d antecedent", elimidx);
      for (r = c->nodes; (lit = r->lit); r++)
	if (abs (lit) != elimidx)
	  push_literal (lit);
      LOGCLAUSE (d, "%d antecedent", -elimidx);
      for (r = d->nodes; (lit = r->lit); r++)
	if (abs (lit) != elimidx)
	  push_literal (lit);
      if (!lookup_clause ()) {
        QRAT_TRACE_RATA_FROM_STACK0("var elimination");
        if (trivial_clause ()) { LOG ("resolvent is trivial"); num_lits = 0; }
        else { LOG ("non-trivial"); add_clause (); }
      } else num_lits = 0;
    }
  }
  LOG ("deleting clauses with %d", elimidx);
  for (p = lit2occ (elimidx)->first; p; p = next) {
    next = p->next;
    qrat_lit = elimidx;
    QRAT_TRACE_RATE_FROM_CLAUSE(p->clause,"var elimination");
    delete_clause (p->clause);
  }
  LOG ("deleting clauses with %d", -elimidx);
  for (p = lit2occ (-elimidx)->first; p; p = next) {
    next = p->next;
    qrat_lit = -elimidx;
    QRAT_TRACE_RATE_FROM_CLAUSE(p->clause,"var elimination");
    delete_clause (p->clause);
  }
  eliminated++;
  assert (isfree (elimidx));
  tag_lit (elimidx, ELIMINATED);
  assert (remaining > 0);
  remaining--;
  LOG ("eliminated %d remaining %d", elimidx, remaining);
}

static void elim_idx (int idx) {
  int limit;
  assert (0 < idx);
  assert (!deref (idx));
  assert (!elimidx);
  if(bce) LOG ("TRYING to block clauses on idx %d", idx);
  block_lit (idx);
  if (trail_flushed ()) {
    block_lit (-idx);
    if (trail_flushed ()) {
      limit = lit2occ (idx)->count + lit2occ (-idx)->count;
      if (limit <= elimoccs) {
	limit += excess;
	LOG ("TRYING to eliminate %d clauses with idx %d in scope %d", 
	     limit, idx, lit2scope (idx)->order);
	assert (!elimidx);
	elimidx = idx;
	if (try_to_resolve_away (limit)) resolve_away (idx);
	assert (elimidx == idx);
	elimidx = 0;
      }
    }
  }
}

static int backward_subsumes (Clause * clause, Clause * other) {
  int lit, count, except, tmp;
  double start = seconds();
  Node * p;
  assert (clause != other);
  assert (clause->size <= bwmax1size);
  if (other->size > bwmax2size) return 0;
  if (clause->size >= other->size) return 0;
  bw.sig1.lookups++;
  if (clause->sig & ~other->sig) { bw.sig1.hits++; return 0; }
  count = clause->size;
  except = other->size - count;
  for (p = other->nodes; except >= 0 && (lit = p->lit); p++)
    if ((tmp = lit2var (lit)->submark) == lit) {
      if (!--count) return 1;
    } else if (tmp == -lit) return 0;
    else except--;
  subsTime += (seconds() - start);
  return 0;
}

static int backward_self_subsumes (Clause * clause, Clause * other) {
  int lit, count, tmp, except, res;
  Node * p;
  assert (clause != other);
  assert (clause->size <= bwmax1size);
  if (other->size > bwmax2size) return 0;
  if (clause->size > other->size) return 0;
  bw.sig1.lookups++;
  if (clause->sig & ~other->sig) { bw.sig1.hits++; return 0; }
  count = clause->size;
  except = other->size - count;
  res = 0;
  for (p = other->nodes; except >= 0 && (lit = p->lit); p++)
    if ((tmp = lit2var (lit)->submark) == lit) {
      if (!--count) return res;
    } else if (tmp == -lit) {
      if (res) return 0;
      res = lit;
      if (!--count) return res;
    } else except--;
  return 0;
}

static void check_all_unsubmarked (void) {
#if 0
#warning "expensive checking that all 'submark' flags are clear enabled"
  int idx;
  for (idx = 1; idx <= num_vars; idx++)
    assert (!vars[idx].submark);
#endif
}

static void submark_clause (Clause * clause) {
  Node * p;
  int lit;
  check_all_unsubmarked ();
  for (p = clause->nodes; (lit = p->lit); p++)
    submark_lit (lit);
}

static void unsubmark_clause (Clause * clause) {
  Node * p;
  int lit;
  for (p = clause->nodes; (lit = p->lit); p++)
    unsubmark_lit (lit);
  check_all_unsubmarked ();
}

static void backward_strengthen (Clause * clause, int lit) {
  int other;
#ifndef NDEBUG
  int found;
#endif
  Node * p;
  LOGCLAUSE (clause,
             "backward strengthening by removing %d from clause", lit);
  assert (!(found = 0));
  assert (!num_lits);
  for (p = clause->nodes; (other = p->lit); p++) {
    if (other == lit) { assert ((found = 1)); continue; }
    assert (num_lits < num_vars);
    lits[num_lits++] = other;
  }
  assert (found);
  assert (num_lits + 1 == clause->size);
  if (!lookup_clause ()) {
    QRAT_TRACE_RATA_FROM_STACK0("backward strengthening"); 
  }
  QRAT_TRACE_RATE_FROM_CLAUSE(clause,"backward strengthening");
  if (trivial_clause ()) {
    num_lits = 0;
  }
  else add_clause ();
  delete_clause (clause);
  strengthened_clauses++;
  backward_strengthened_clauses++;
}

static int least_occurring_lit_except (Clause * clause, int except) {
  int best = INT_MAX, tmp, start = 0, lit;
  Node * p;
  assert (clause->size > 1);
  for (p = clause->nodes; (lit = p->lit); p++) {
    if (lit == except) continue;
    tmp = lit2occ (lit)->count;
    if (best <= tmp) continue;
    start = lit;
    best = tmp;
  }
  assert (start);
  assert (best < INT_MAX);
  LOG ("literal %d has shortest occurrence list of length %d except %d",
       start, best, except);
  assert (best >= 1);
  return start;
}

static void backward (Clause * clause) {
  int lit, first, second, i;
  Node * p, * next;
  Clause * other;
  Occ * occ;
  Sig sig;
  if (clause->size > bwmax1size) return;
  first = least_occurring_lit_except (clause, 0);
  if (lit2occ (first)->count > bwmaxoccs) return;
  sig = ~0llu;
  for (p = clause->nodes; (lit = p->lit); p++)
    sig &= bwsigs [ abs (lit) ];
  LOG ("clause sig2  %016llx", clause->sig);
  LOG ("intersection %016llx", sig);
  bw.sig2.lookups++;
  if (clause->sig & ~sig) { bw.sig2.hits++; goto DONE; }
  LOGCLAUSE (clause, "backward subsumption with clause");
  submark_clause (clause);
  occ = lit2occ (first);
  for (p = occ->first; p; p = next) {
    next = p->next;
    other = p->clause;
    if (other == clause) continue;
    if (!backward_subsumes (clause, other)) continue;
    subsumed_clauses++;
    backward_subsumed_clauses++;
    LOGCLAUSE (other, "backward subsumed clause");
    QRAT_TRACE_RATE_FROM_CLAUSE(other,"backward subsumption");
    delete_clause (other);
  }
  for (i = 1; i <= 2; i++) {
    if (i == 2) {
      second = least_occurring_lit_except (clause, first);
      occ = lit2occ (second);
    }

    if (occ->count > bwmaxoccs)
      break;                         // added as suggestion von A. van Gelder

    for (p = occ->first; p; p = next) {
      next = p->next;
      other = p->clause;
      if (other == clause) continue;
      lit = backward_self_subsumes (clause, other);
      if (!lit) continue;
      LOG ("backward self subsuming resolution on %d", lit);
      LOGCLAUSE (clause, "1st backward self subsuming antecendent");
      LOGCLAUSE (other, "2nd backward self subsuming antecendent");
      assert (clause->size <= other->size);
      if (clause->size == other->size) {
	backward_strengthen (other, lit);
	unsubmark_clause (clause);
LOG ("double backward self subsumption strengthens subsuming clause");
	backward_strengthen (clause, -lit);
	clause = 0;
	return;
      } else backward_strengthen (other, lit);
    }
  }
  unsubmark_clause (clause);
DONE:
  assert (clause);
  for (p = clause->nodes; (lit = p->lit); p++)
    bwsigs [ abs (lit) ] |= clause->sig;
}

static void enlarge_stack (void) {
  int new_size = szstack ? 2*szstack : 1;
  RSZ (stack, szstack, new_size);
  szstack = new_size;
}

static void push_stack (int elem) {
  if (szstack == nstack) enlarge_stack ();
  LOG("pushing literal on stack %d ",elem);
  stack[nstack++] = elem;
}

static void enlarge_aux (void) {
  int new_size = szaux ? 2*szaux : 1;
  RSZ (aux, szaux, new_size);
  szaux = new_size;
}

static void push_aux (int elem) {
  if (szaux == naux) enlarge_aux ();
  aux[naux++] = elem;
}

static void mv_vstack_to_lstack () {
  int i; 

  if (qrat_lit) {
    push_literal (qrat_lit); 
  }

  for (i=0; i<nstack; i++) {
    if ((stack[i] != qrat_lit)) push_literal (stack[i]);
  }


  qrat_lit = 0;

}

static int hidden_tautology (Clause * c) {
  int redundant, lit, other, next, props, add, tmp, i, j, order;
#ifndef NDEBUG
  int found;
#endif
  int red_lit = 0;
  int found_cc = 0;
  Node * p, * q, * r;
  Occ * pocc, * nocc;
  double startHBCE;
  double startHT;
  double startCCE;
  int blocking_lit = 0;
  int cblocking_lit = 0;
  int idx;
  Var *v;
  Clause * d;

  if (!hte && !cce) return 0;
  LOGCLAUSE (c, "trying hidden tautology elimination of clause");
  assert (!nstack);
  assert (!clause_stack_top);

  for (p = c->nodes; (lit = p->lit); p++) 
    push_stack (lit), mark_lit (lit);

  redundant = next = props = 0;
  while (next < nstack) {
    if (redundant) goto DONE;
    if (++props > htesteps) goto DONE;
    lit = stack[next++];
    if (partial_assignment &&
        vars[abs(lit)].scope->order == assigned_scope) continue;
    assert (lit2var (lit)->mark == lit);
    pocc = lit2occ (lit);

    if (hte && pocc->count <= hteoccs) {
      startHT = seconds();
      for (q = pocc->first; q; q = q->next) {
	d = q->clause;
	if (d == c) continue;
	if (d->size > htesize) continue;
	add = 0;
	assert (!(found = 0));
	for (r = d->nodes; (other = r->lit); r++) {
	  if (other == lit) { assert ((found = 1)); continue; }
	  assert (other != lit);
	  tmp = lit2var (other)->mark;
	  if (tmp == other) continue;
	  if (add || tmp == -other) { add = INT_MAX; break; }
	  add = -other;
	}

	assert (other || add == INT_MAX || found);
	if (add == INT_MAX) continue;
	if (!add) { 
	  redundant = 1;
	  LOGCLAUSE (d, "hiddenly subsuming clause");
	  goto DONE; 
	}

        if (partial_assignment &&
	    vars [abs(add)].scope->order == assigned_scope) continue;
	LOGCLAUSE (d, "added hidden literal %d through clause", add);
	hlas++;
	tmp = lit2var (add)->mark;

        
	if (tmp == -add) {
          LOGCLAUSE(d,"redundant clause"); 
          redundant = 1; 
          goto DONE; 
        }
	for (r = d->nodes; (other = r->lit); r++) {
	  if (other != -add) {
            lit2var (other) -> mark4 = 1;
          }
	}
	assert (!tmp);
	mark_lit (add);
	push_stack (add);
        if (qrat_file) {
         assert (!num_lits);
          LOGCLAUSE(c, "%d adding literal %d to clause", add, clause_stack_top);
          qrat_lit = 0;
          mv_vstack_to_lstack ();
          clause_stack_push ();
          qrat_lit = 0;
          num_lits = 0;
        }
      }

      hteTime += (seconds() - startHT);
    }
    if (cce &&
        existential (lit) &&
        (!partial_assignment || (lit2order(lit) != assigned_scope) )) {
      startCCE = seconds();
      nocc = lit2occ (-lit);
      q = nocc->first;
      if (q && nocc->count <= hteoccs) {
	assert (!naux);
	order = lit2order (lit);
	assert (!(found = 0));
	d = q->clause;
	for (r = d->nodes; (other = r->lit); r++) {
	  if (other == -lit) { assert ((found = 1)); continue; }
	  if (lit2var (other)->mark == other) continue;
	  if (lit2order (other) > order) continue;
          if (partial_assignment &&
	      vars [abs(other)].scope->order == assigned_scope) continue;
	  submark_lit (other);
	  push_aux (other);
	}
	assert (found);
	for (q = q->next; naux && q; q = q->next) {
	  d = q->clause;
	  assert (!(found = 0));
	  for (r = d->nodes; (other = r->lit); r++) {
	    if (other == -lit) { assert ((found = 1)); continue; }
	    if (lit2var (other)->mark == other) continue;
	    if (lit2order (other) > order) continue;
	    tmp = lit2var (other)->submark;
	    if (tmp != other) continue;
	    unsubmark_lit (other);
	  }
	  j = 0;
	  for (i = 0; i < naux; i++) {
	    other = aux[i];
	    tmp = lit2var (other)->submark;
	    if (tmp == other) {
	      unsubmark_lit (other);
	    } else {
	      assert (!tmp);
	      submark_lit (other);
	      aux[j++] = other;
	    }
	  }
	  naux = j;
	}
	while (naux > 0) {
	  other = aux[--naux];
	  unsubmark_lit (other);
          if (partial_assignment &&
	      vars [abs(other)].scope->order == assigned_scope) continue;
	  if (redundant) continue;
	  tmp = lit2var (other)->mark;
	  LOG ("adding covered literal %d for pivot %d", other, lit);
	  clas++;
	  if (tmp) { 
	    cblocking_lit = lit;
            blocking_lit = lit;
            LOG("redundant");
            assert (tmp == -other); 
            redundant = 1; 
	    push_stack (other);
            continue; 
          }
          assert (!tmp);
	  mark_lit (other); 

	  push_stack (other);

          if (qrat_file) {
            qrat_lit = lit; 
            blocking_lit = lit; 
            mv_vstack_to_lstack ();
            clause_stack_push ();
            num_lits = 0;
            qrat_lit = 0;
            found_cc = 1;
          }

	}
	check_all_unsubmarked ();
      }
      cceTime += (seconds() - startCCE);
    }
  }
DONE:
  LOG ("hidden tautology check finished after %d steps", props);
  if (redundant) {
    LOGCLAUSE (c, "hidden tautological clause");
    hidden_tautologies++;
  } else if ((hbce && bce) || (hble && ble)) {
   startHBCE = seconds();
   blocking_lit = 0;
    for (i = 0; !redundant && i < nstack; i++) {
      lit = stack[i];
      if (!existential (lit) && !(hble && ble)) continue;
      if (existential (lit) && !(hbce && bce)) continue;
      if (partial_assignment && vars[abs(lit)].scope->order == assigned_scope)
	continue;
      if (lit2occ (-lit)->count > blkmax1occs) continue;
      LOG ("check whether literal %d blocks extended clause", lit);
      
      if (existential (lit) || !red_lit) {
        redundant = block_clause_aux (lit);
      }
      if (universal (lit) && redundant && !red_lit) {
        redundant = 0;
        if (!(lit2var (lit) -> mark4)) { 
          red_lit = lit;
          LOG("found hidden blocked literal %d", red_lit);
          hidden_blocked_literals++;
        }
      }
    }
    if (redundant) {
      hidden_blocked_clauses++;
      LOGCLAUSE (c, "hidden blocked clause on literal %d", lit);
      blocking_lit = lit;
      cblocking_lit = lit;
    }
    hbceTime += (seconds() - startHBCE);
  }

  int nstack2 = nstack; 
  while (nstack2 > 0) unmark_lit (stack[--nstack2]);
  check_all_unmarked ();
  check_all_unsubmarked ();
  

  if (!redundant && !red_lit) { 
    if (qrat_file) {
      for (i=0; i<clause_stack_top; i++) {
        DELN(clause_stack[i], clause_stack[i][0]+1);
      }
      clause_stack_top = 0;
    }
    for (idx = 1; idx <= num_vars; idx++) {
      v = lit2var (idx);
      v->mark4 = 0;
    }
    nstack = 0;
    return 0;
  }


  if (qrat_file) {
    int j;
    if ((!found_cc && !blocking_lit) || !clause_stack_top) {
      qrat_lit = cblocking_lit;
      QRAT_TRACE_RATE_FROM_CLAUSE(c, "asymmetric taut or subs");
    } else {
      for (i=0; i<clause_stack_top; i++) {
        assert(!num_lits);
        for (j = 1; j < clause_stack[i][0]+1; j++) {
          push_literal (clause_stack[i][j]);
        } 
        QRAT_TRACE_RATA_FROM_STACK0 ("asymmetric or covered literal addition");
        QRAT_TRACE_RATE_FROM_STACK 
          (num_lits-1,num_lits,"asymmetric or covered literal rm");
        num_lits = 0;
      }
      i--;
      for (j = 1; j < clause_stack[i][0]+1; j++) {
        push_literal (clause_stack[i][j]);
      }
      if (blocking_lit) {
        qrat_lit = blocking_lit; 
        if (!lookup_clause ()) QRAT_TRACE_RATE_FROM_STACK0 ("last asymmetric or covered literal removal ");
      } else {
        // if (red_lit) ...
        // TODO BLE
      }
      num_lits = 0;  
    }


    for (i=0; i<clause_stack_top; i++) {
      DELN(clause_stack[i], clause_stack[i][0]+1);
      clause_stack[i] = NULL;
    }
  }
  clause_stack_top = 0;
  if (!redundant && red_lit) {
    LOGCLAUSE (c,"removing hidden blocked lit %d from", red_lit);
   // for (r = c->nodes; (other = r->lit); r++) {
    while (nstack > 0) {
      other = stack[ --nstack2];
      if (other != red_lit) {
        push_literal (other);
      } 
  
    }
    add_clause ();
    delete_clause (c);
  } else {
    delete_clause (c);
  }
  for (idx = 1; idx <= num_vars; idx++) {
    v = lit2var (idx);
    v->mark4 = 0;
  }
  nstack = 0;
  return 1;
}

#if 0 && !defined(NDEBUG)
#warning "expensive subsumed checking code enabled"
static int really_subsumes (Clause * a, Clause * b) {
  int res, lit;
  Node * p;
  if (a->size > b->size) return 0;
  mark_clause (b);
  res = 1;
  for (p = a->nodes; res && (lit = p->lit); p++)
    res = (lit2var (lit)->mark == lit);
  unmark_clause (b);
  return res;
}

static int really_strengthen (Clause * a, Clause * b) {
  int res, lit, tmp, pivot;
  Node * p;
  if (a->size > b->size) return 0;
  mark_clause (b);
  res = 1;
  pivot = 0;
  for (p = a->nodes; res && (lit = p->lit); p++) {
    tmp = lit2var (lit)->mark;
    if (tmp == lit) continue;
    else if (tmp != -lit) res = 0;
    else if (pivot) res = 0;
    else pivot = lit;
  }
  unmark_clause (b);
  return res ? pivot : 0;
}

static void check_subsumed (void) {
  Clause * p, * q;
  for (p = first_clause; p; p = p->next)
    for (q = first_clause; q; q = q->next) {
      if (p != q) {
	assert (!really_subsumes (p, q));
	assert (!really_strengthen (p, q));
      } else assert (really_subsumes (p, q));
    }
}
#else
static void check_subsumed (void) { }
#endif

static void flush_queue (int outer) {
  Clause * clause;
  double start;
  if (!queue) return;
  start = outer ? seconds () : 0.0;
  LOG ("starting to flush queue with %d clauses", nqueue);
  if (outer) start_progress ("backward subsumption queue", &nqueue);
  while ((clause = queue)) {
    dequeue (clause);
    if (!hidden_tautology (clause)) backward (clause);
    flush_trail ();
    if (empty_clause) break;
  }
  assert (empty_clause || !nqueue);
  if (outer) stop_progress ();
  check_subsumed ();
  if (!outer) return;
  msg ("flushed backward subsumption queue in %.1f seconds",
       seconds () - start);
  if (verbose) log_pruned_scopes ();
}

static int pop_literal (void) {
  assert (num_lits > 0);
  return lits[--num_lits];
}

static void dfs_clean (void) {
  memset (dfsi - num_vars, 0, (2*num_vars + 1) * sizeof *dfsi);
  memset (mindfsi - num_vars, 0, (2*num_vars + 1) * sizeof *mindfsi);
  memset (repr - num_vars, 0, (2*num_vars + 1) * sizeof *repr);
}

static int cmporder (int a, int b) {
  int res;
  if ((res = lit2order (a) - lit2order (b))) return res;
  if ((res = abs (a) - abs (b))) return res;
  return b - a;
}

static int subst_clause (Clause * c) {
  int lit, tmp, res;
  Node * p;
  assert (!num_lits);
  res = 0;

  LOGCLAUSE(c, "trying subst clause");
  for (p = c->nodes; (lit = p->lit); p++) {
    tmp = repr[lit];
    if (partial_assignment && vars[abs(tmp)].scope->order == assigned_scope) 
      tmp = lit;
    assert (tmp);
    if (tmp != lit) {
      res = 1;
    }
    push_literal (tmp);
  }
  if (!res) { num_lits = 0; return 0; }

  if (!lookup_clause ()) {
    qrat_lit = 0;
    QRAT_TRACE_RATA_FROM_STACK0("equivalence substitution");
  }
  QRAT_TRACE_RATE_FROM_CLAUSE(c,"equivalence substitution");

  LOGCLAUSE (c, "substituting clause");
  if (trivial_clause ()) {
    LOG ("substituted clause becomes trivial");
    num_lits = 0;
  } else add_clause ();
  return 1;
}

static void flush_vars (void) {
  int idx, pos, neg;
  for (idx = 1; !empty_clause && idx <= num_vars; idx++) {
    if (!isfree (idx)) continue;
    LOG("flushing var %d",idx);
    pos = lit2occ (idx)->count; 
    neg = lit2occ (-idx)->count; 
    if (!pos && !neg) zombie (idx);
    if (existential (idx)) {
      if (!neg) unet (idx); else if (!pos) unet (-idx);
    } else {
      if (!neg) unate (idx); else if (!pos) unate (-idx);
    }
  }
}

int count_size (Clause * c) {
  Node * n;

  int i = 0;
  for (n=c->nodes; n->lit;n++) {
    i++;
  }


  return i;

}

static int mark_stack_lits_without (int min, int offset, int * st) {
  int lit, i, j = 0;
  Var * v;
  for (i=0; i < num_lits; i++) {
    if ((i >= min) && (i < min+offset)) continue;
    lit = lits[i];
    v = lit2var (lit);

    if ((!v->lmark) && (lit > 0)) st[j++] = lit;
    if ((!v->lmark2) && (lit < 0)) st[j++] = lit;
    if (lit > 0) v->lmark = lit;
    else v->lmark2 = lit;
  }
  return j;
}


static int mark_stack_lits (int * st) {
  int lit, i, j = 0;
  Var * v;
  for (i=0; i < num_lits; i++) {
    lit = lits[i];
    v = lit2var (lit);
    if ((!v->lmark) && (lit > 0)) st[j++] = lit;
    if ((!v->lmark2) && (lit < 0)) st[j++] = lit;

    if (lit > 0) v->lmark = lit;
    else v->lmark2 = lit;
    LOG("stack lit: %d", lit);
  }

  return j;

}

static void unmark_stack_lits () {
  int lit, i;
  Var * v;
  for (i=0; i < num_lits; i++) {
    lit = lits[i];
    v = lit2var (lit);
    v->lmark = 0;
    v->lmark2 = 0;
  }

}

static Clause * lookup_clause_without (int from, int to) {
  int lit, is_clause;
  Clause * c;
  Occ * o;
  Node * n, * p;
  Var * v;
  
  LOG("num_lits. %d %d %d", num_lits, from , to );

  if (!num_lits || ((num_lits-(to-from)) <= 0)) return first_clause;

  if (no_lookup) return NULL;
  int * slits, slits_size;
  NEWN(slits, num_lits); 

  slits_size = mark_stack_lits_without (from, to, slits);
  Sig sig = sig_lits_without (from, to, slits, slits_size);


  DELN(slits,num_lits);

  LOG("looking up clause with signature  %016llx in stack range %d %d %d", 
     sig, from, to, slits[0]);

 
  lit = least_occuring_lit_without (from, to);
 
  o = lit2occ (lit);
  LOG("checking lit %d",lit);
  assert(o);

  for (n=o->first;n; n=n->next) {
   c = n->clause;
   LOGCLAUSE(c,"checking clause");
   if (sig != c->sig) continue;
   if ((c->size != (slits_size))) continue;

   is_clause = 1;

   for (p=c->nodes;(lit=p->lit);p++) {
     v = lit2var (lit);
     if ((v->lmark != lit) && (v->lmark2 != lit)) {
       is_clause = 0;
     }
   }
   if (!is_clause) continue;

   unmark_stack_lits ();
   return c;
  }

  unmark_stack_lits ();
  return NULL;
}




static Clause * lookup_clause () {
  int lit, is_clause;
  Clause * c;
  Occ * o;
  Node * n, * p;
  Var * v;

  
  if (num_lits == 0) return empty_clause;
  if (no_lookup) return NULL;
  if (!num_lits ) return first_clause;


  int * slits, slits_size;
  NEWN(slits, num_lits); 
  slits_size = mark_stack_lits (slits);
 
  Sig sig = sig_lits2 (slits, slits_size);
  LOG("looking up clause with signature  %016llx", sig);

  DELN(slits, num_lits);
  lit = least_occuring_lit ();

  o = lit2occ (lit);
  LOG("checking lit %d for lookup clause",lit);
  assert(o);

  for (n=o->first;n; n=n->next) {
   c = n->clause;
   LOGCLAUSE(c,"looking up ");
   if (sig != c->sig) {
    LOG("%d %d",slits_size, c->size); 
    LOG("looking up clause with signature  %016llx", c->sig);
     continue;
   }
   if ((c->size != slits_size)) {
     continue;
   }
   is_clause = 1;

   for (p=c->nodes;(lit=p->lit);p++) {
     v = lit2var (lit);
     if ((v->lmark != lit) && (v->lmark2 != lit)) {
       is_clause = 0;
     }
   }
   if (!is_clause) continue;

   unmark_stack_lits ();
   LOGCLAUSE(c,"found clause");
   return c;
  }

  unmark_stack_lits ();
  return NULL;
}


static void derive_empty_clause (int contr) {
  Occ * occ;
  Node * n;
  Clause * c, * d;
  int sz;
  int current = 0;
  Clause * cache_empty = empty_clause;
  int lit, lit2; 
  int trivial = 0;

  if (!qrat_file) return;

  LOG("deriving empty clause %d",contr);

  assert (contr);
  assert (empty_clause);
  assert (!num_lits);
  assert (!substituting);

  empty_clause = NULL;
  assert (lit2occ(contr));
  assert (lit2occ(-contr));

  occ = lit2occ (contr);
  assert (!clause_stack_top);
  substituting2 = 1;

		// put all binary clauses with contradicting lit on stack
  for (n=occ->first;n;n=n->next) {
    c = n->clause;
    if (c->size != 2) continue;
    if (abs(contr) == abs(c->nodes[0].lit)) {
      push_literal (c->nodes[1].lit);
      push_literal (c->nodes[0].lit);
    } else {
      push_literal (c->nodes[0].lit);
      push_literal (c->nodes[1].lit);
    }
    clause_stack_push();
    num_lits = 0;
  
  }
  
  while (current < clause_stack_top) {


    sz = clause_stack[current][0];
    lit = clause_stack[current][1];
    lit2 = clause_stack[current][2];


    assert (!num_lits);

    occ = lit2occ (-lit);
    for (n=occ->first;n;n=n->next) {
      c = n->clause;
      if (c->size != 2) continue;
      if (abs(lit) == abs(c->nodes[0].lit)) {
        push_literal (c->nodes[1].lit);
      } else {
        push_literal (c->nodes[0].lit);
      }

      if (sz > 1) push_literal(lit2);

        if (lits[0] == lits[1]) {
          num_lits = 1;
          sz = 1;
        }
 
      if (!lookup_clause ()) {

        if ((sz > 1) && (lit2var(lit2)->scope->type < 0) && 
            (lit2var(lit2)->scope->type <= lit2var(lits[0])->scope->type)) {
          QRAT_TRACE_RATA_FROM_STACK0_WITHOUT_CHECK ("contr: adding clause");
          QRAT_TRACE_EUR_FROM_STACK0(lit2, "contr: rm clause");
          num_lits--;
        } else {
        QRAT_TRACE_RATA_FROM_STACK0_WITHOUT_CHECK ("contr: adding clause");
        }
        clause_stack_push ();
        
        if (!trivial_clause ()) {
          trivial = 1;
        } 
        add_clause ();

      }
      if (!trivial) {

        d = lookup_clause ();
        if (d) d->cmark2 = 1;


      } else trivial = 0;

      num_lits = 0;
    }
    num_lits = 0;
    current++;
  }

  int i;

  for (i=0; i<clause_stack_top;i++) {
    DELN(clause_stack[i], clause_stack[i][0]+1);
  }

  empty_clause = cache_empty;
}


static void subst (void) {
  Clause * last, * p, * next, * prev;
  int idx, tmp, count = 0, lit, other;
  Var * v;
  Occ * occ;
  Node * n;
  Clause * c;
 int lit2; 
 int count_clauses = 0;
 int repr_lit;

  assert (!empty_clause);
  assert (!num_lits);
  assert (!substituting);

  for (idx = 1; idx <= num_vars; idx++) {
    tmp = repr[idx];
    if (!tmp) continue;
    if (tmp == idx) continue;
    if (partial_assignment && vars[abs(tmp)].scope->order == assigned_scope) continue;
    v = vars + idx;
    assert (v->tag == FREE);
    substituted++;
    tag_var (v, SUBSTITUTED);
    if (partial_assignment && vars[idx].scope->order == assigned_scope) {
        subst_vals[idx] = tmp;
    }
    assert (remaining > 0);
    remaining--;
    LOG ("substituting %d by %d remaining %d", idx, tmp, remaining);
  }

  substituting = 1;
  last = last_clause;
  prev = NULL;
  if (!qrat_file) {
    for (p = first_clause; !empty_clause && prev != last; p = next) {
      next = p->next;
      prev = p;
      if (!subst_clause (p)) continue;
      delete_clause (p);
      count++;
    }
    LOG ("substituted %d clauses", count);
    assert (substituting);
    substituting = 0;
    flush_trail ();
    return;
  }

  assert (substituting);
  for (p = first_clause; !empty_clause && prev != last; p = next) {
    next = p->next;
    prev = p; 				
			/* substitute the non-binary clauses and the 
			   binary clauses which are not involved in an 
			   equivalency cycle, i.e., we assume the 
			   two literals have the same represenatative.
			   We assume that the equivlaency is not 
			   contradictionary.  */
    if (p->size == 2) {
      lit = repr[p->nodes[0].lit];
      lit2 = repr[p->nodes[1].lit];
      if (lit && (abs(lit) == abs(lit2)) && (lit != lit2) && lit2 ) {
        count_clauses++;
        continue;
      }
    }

    if (!subst_clause (p)) continue;
    delete_clause (p);
    count++;
  }


			/* now eliminate the binary clauses which form 
			   the equivalencies. Therefore, we use 
                           some kind of variable elimination */


  substituting2 = 1;	// hinders forward subsumption, strength, universal red. 			// otherwise we would loose necessary clauses		

  int count_leak = 0;	// debugging variable
  int idx2;
  int b1, b2;

  LOG ("starting with QRAT of equivalences");


  for (idx = 1; idx <= num_vars; idx++) {
    repr_lit = repr [idx];

    if (!repr_lit) continue;

    if (lit2var(repr_lit)->mark4) continue; 	// repr_lit hasn't been 
						// considered before and
    if (idx == repr_lit) continue;		// repr_lit is really a repr.
              
 
    occ = lit2occ (repr_lit);
    lit2var(repr_lit)->mark4 = 1 ; 
    assert (!nstack);    

    for (idx2 = idx; idx2 <= num_vars; idx2++) {
      if (abs(repr[idx2]) == abs(repr_lit)) {
        push_stack(idx2);
      } 
    }

    for (b1 = 0; b1 < nstack; b1++) {
      for (b2 = 0; b2 < nstack-b1-1; b2++) {
        lit = stack[b2];
        lit2 = stack[b2+1];
        if (lit2var (lit)->scope->order < lit2var (lit2)->scope->order) {
          stack[b2] = lit2;
          stack[b2+1] = lit;
        }
      }  

    }

    int current = 0;
    
   // stack contains the list of variables to be eliminated

    int pivot; 

    while (current < nstack) {
      pivot = stack [current];		// next variable to be eliminated


      v = lit2var (pivot);

      if (v->mark4) {			// pivot has not been considered before
        current++;
        continue;
      }      

      v->mark4 = 1;

      assert(!clause_stack_top);
					// get all clauses with 
					// negative occurrences of pivot
					// necessary for crossproduct
      occ = lit2occ (-pivot); 

      for (n=occ->first; n; n=n->next) {
        c = n->clause;

        if (c->size != 2) continue;

        if (c->cmark2) continue;

        lit = c->nodes[0].lit;
        lit2 = c->nodes[1].lit;

        if  ((abs (repr[lit])) != abs (repr[lit2])) {
	  continue;
        }
        assert ((abs (repr[lit])) == abs (repr[lit2]));

        assert (!num_lits);

        if (lit == -pivot) {
          push_literal (lit);
          push_literal (lit2); 
        } else {
          assert (lit2 == -pivot);
          push_literal (lit2); 
          push_literal (lit);
        }
        clause_stack_push ();
        num_lits = 0;
      }
      

      occ = lit2occ (pivot);

      for (n=occ->first; n; n=n->next) {
        c = n->clause;
        if (c->cmark2) continue;
        if (c->size != 2) continue;
        lit = c->nodes[0].lit;
        lit2 = c->nodes[1].lit;

        if ((abs (repr[lit])) != abs (repr[lit2])) continue;

        if (lit2 == pivot) {
          lit2 = lit; 
          lit = pivot;
        }


        other = 0;

	/* get all resolvents for clause c */

        for (other=0; other<clause_stack_top; other++) {

          assert (clause_stack[other][0] == 2);
          assert (!num_lits);

          push_literal (lit2);			// the new clause
          push_literal (clause_stack[other][2]);

          assert (num_lits == 2);
          qrat_lit = 0;

          if (!lookup_clause ()) {
            QRAT_TRACE_RATA_FROM_STACK0("eq subst: adding resolvent ");

            if (!trivial_clause ()) { 
              add_clause ();
              count_leak++;
            }
          }
            num_lits = 0;
        }

					// now we can eliminate clause c
        qrat_lit = pivot;
        QRAT_TRACE_RATE_FROM_CLAUSE(c,"eq subst: rm first antecedent");
        count_clauses--;
        c->cmark2 = 1;
      } 
					// eliminate the other antecedents
      occ = lit2occ (-pivot);
      for (n=occ->first; n; n=n->next) {
        c = n->clause;
        if (c->cmark2) continue;

        if (c->size == 1) {		//ignore units
          if (abs(repr[c->nodes[0].lit]) == abs(repr_lit)) {
            c->cmark2 = 1;
         }
          continue;
        }
 
        if (c->size != 2) continue;

        lit = c->nodes[0].lit;
        lit2 = c->nodes[1].lit;

        if ((abs (repr[lit]) != abs (repr[lit2])) &&
            (abs (repr[lit] != abs(repr_lit)))) continue;

        qrat_lit = -pivot;
        QRAT_TRACE_RATE_FROM_CLAUSE(c,"eq subst: rm second antecedent");
        c->cmark2 = 1;
     }
      int i;
					// free the stack
      for (i=0; i<clause_stack_top;i++) {
        DELN(clause_stack[i], clause_stack[i][0]+1);
      }
      clause_stack_top = 0;
      current++;
    }
    nstack = 0;
  }


  last = last_clause;
  prev = NULL;



  for (p = first_clause; !empty_clause && prev != last; p = next) {
    next = p->next;
    prev = p;
    if (p->size == 2) {
      if (repr[p->nodes[0].lit] && (abs(repr[p->nodes[0].lit]) == 
        abs(repr[p->nodes[1].lit]) )) {
        delete_clause (p);
        count_leak--; 
        continue;
      }
    }
    if (p->size == 1) {
      lit = p->nodes[0].lit;
      v = lit2var (lit); 
      if (v->tag == SUBSTITUTED) {
        assert(!num_lits); 
        push_literal (lit); 
        LOG("unit by subst");
        if (!lookup_clause()) QRAT_TRACE_RATA_UNIT(lit, "unit by subst");
        assign (lit); 
        num_lits = 0;
      }
    }
  }
 

  nstack = 0;
  num_lits = 0;

  for (idx = 1; idx <= num_vars; idx++) {
    v = lit2var (idx);
    v->mark4 = 0;
  }

  LOG ("substituted %d clauses", count);
  assert (substituting);
  substituting = 0;
  substituting2 = 0;
  flush_vars ();
  flush_trail ();

}

static int eqres (int outer) {
  int start, current, idx, count, pos, child, min, max, tmp, i;
  double started;
  Clause * c;
  Occ * occ;
  Node * p;
  count = 0;
  int contr = 0;


  if (!eq) return 0;
  assert (added_binary_clauses_at_last_eqround <= added_binary_clauses);
  if (added_binary_clauses_at_last_eqround == added_binary_clauses) {
    return 0;
  }
  added_binary_clauses_at_last_eqround = added_binary_clauses;

  assert (!empty_clause);
  assert (trail_flushed ());
  assert (!queue);
  started = seconds ();
  eqrounds++;
  idx = count = 0;

  for (start = -num_vars; !empty_clause && start <= num_vars; start++) {
    if (!start) continue;
    if (!isfree (start)) continue;

    if (dfsi[start]) continue;
    assert (!num_lits);
    assert (!nstack);
    push_literal (start);
    while (num_lits > 0) {
      current = pop_literal ();
      if (current) {
	if (dfsi[current]) continue;
	push_stack (current);
	push_literal (current);
	push_literal (0);
	mindfsi[current] = dfsi[current] = ++idx;
	assert (idx < INT_MAX);
	LOG ("dfsi %d = %d", current, idx);
	occ = lit2occ (-current);
	for (p = occ->first; p; p = p->next) {
	  c = p->clause;
	  if (c->size != 2) continue;
	  assert (p->lit == -current);
	  pos = (c->nodes[1].lit == -current);
	  assert (c->nodes[pos].lit == -current);
	  child = c->nodes[!pos].lit;
	  if (dfsi[child]) continue;
	  push_literal (child);
	}
      } else {
	current = pop_literal ();
	min = mindfsi[current];
	assert (min == dfsi[current]);
	occ = lit2occ (-current);
	for (p = occ->first; p; p = p->next) {
	  c = p->clause;
	  if (c->size != 2) continue;
	  assert (p->lit == -current);
	  pos = (c->nodes[1].lit == -current);
	  assert (c->nodes[pos].lit == -current);
	  child = c->nodes[!pos].lit;
	  tmp = mindfsi[child];
	  if (tmp >= min) continue;
	  min = tmp;
	}
	mindfsi[current] = min;
#ifndef NLOG
	{
	  int cmpch = '=';
	  if (min < dfsi[current]) cmpch = '<';
	  if (min > dfsi[current]) cmpch = '>';
	  LOG ("mindfsi %d = %d   %c%c   %d = dfsi %d", 
	       current, min, cmpch, cmpch, dfsi[current], current);
	}
#endif
	assert (min <= dfsi[current]);
	if (min < dfsi[current]) continue;
	pos = nstack;
	while (stack[--pos] != current)
	  assert (pos > 0);
	max = 0;
	for (i = pos; i < nstack; i++)
	  if (universal (tmp = stack[i]) && 
	      (!max || cmporder (max, tmp) < 0)) max = tmp;
	min = current;
	for (i = pos + 1; i < nstack; i++)
	  if (cmporder ((tmp = stack[i]), min) < 0) min = tmp;
	for (i = pos; !empty_clause && i < nstack; i++) {
	  repr[tmp = stack[i]] = min;
	  if (tmp != min) count++;
	  mindfsi[tmp] = INT_MAX;
	  LOG ("repr %d = %d", tmp, min);
	  if (max &&
	      tmp != max && 
	      lit2order (tmp) <= lit2order (max)) {
            LOG ("universal representative %d of scope %d", 
	         max, lit2order (max));
            contr = max;
	    LOG ("literal %d of scope %d is equivalent to %d",
	         tmp, lit2order (tmp), max);
GENERATE_EMPTY_CLAUSE:
            num_lits = 0;
	    LOG ("forced to add empty clause");
	    add_clause ();
	  } else if (tmp == -min) {
	    LOG ("%d and %d are both in the same equivalence class",
	         tmp, min);
            contr = tmp;
	    goto GENERATE_EMPTY_CLAUSE;
	  }
	}
	nstack = pos;
      }
    }
  }
  LOG ("found %d equivalent literals", count);
  assert (empty_clause || !(count & 1));
  assert (empty_clause || (!num_lits && !nstack));
  num_lits = nstack = 0;
  if (empty_clause) derive_empty_clause (contr);
  else if (!empty_clause  && count) subst ();
  LOG("eq reasoning done");
  dfs_clean ();
  if (outer || verbose > 1) {
    msg ("found %d equivalent variables in round %d in %.1f seconds",
         count/2, eqrounds, seconds () - started);
    if (verbose) log_pruned_scopes ();
  }

  eqTime += (seconds() - started);
  if (empty_clause) flush_trail ();
  return count;
}

static void check_var_stats (void) {
#ifndef NDEBUG
  int sum_stats = remaining;
  sum_stats += unets;
  sum_stats += unates;
  sum_stats += fixed;
  sum_stats += zombies;
  sum_stats += eliminated;
  sum_stats += substituted;
  sum_stats += expanded;
  assert (sum_stats == num_vars);
#endif
}

static void flush (int outer) {
  flush_trail ();
  if (empty_clause) {
    return;
  }
  flush_queue (outer);
}

static void elim (void) {
  double start = seconds ();
  int idx;
  assert (!empty_clause);
  assert (trail_flushed ());
  assert (!queue);
  start_progress ("elimination queue", &size_schedule);
  do {
    while (!empty_clause && size_schedule) {
      check_var_stats ();
      idx = pop_schedule ();
      if (!isfree (idx)) continue;
      if (partial_assignment && 
	  vars [abs (idx)].scope->order == assigned_scope) continue;
      if (null_occurrences (idx)) { zombie (idx); continue; }
      if (universal (idx)) {
        if (ble) {
          block_lit (idx);
          if (trail_flushed ()) block_lit (-idx);
          continue;
        }
        continue;
      }
      elim_idx (idx);
      flush (0);
    }
    if (!empty_clause && eqres (0)) flush (0);
  } while (!empty_clause && size_schedule);
  stop_progress ();
  msg ("elimination took %.1f seconds", seconds () - start);
  elimTime += (seconds () - start);
}

static int lit2stretch (int lit) { return lit2scope (lit)->stretch; }


static int in_innermost_ublock (int lit) {
  
  assert (universal(lit));

  Var * v = lit2var (lit);
  Scope *s;

  for (s = v->scope->inner; s; s=s->inner) {
    if (s->type < 0) return 0;
  }

  return 1;

}

static int expand_cost_trav (int pivot, int bound) {
  int next, lit, other, tmp, res, sign, occs, stretch;
  Node * p, * q;
  Clause * c;
  Occ * occ;
  Var * v;
  assert (universal (pivot));
  assert (0 < pivot && pivot <= num_vars);
  assert (!nstack);
  occs = lit2occ (pivot)->count + lit2occ (-pivot)->count;
  LOG ("universal %d occurs in %d clauses", pivot, occs);
  res = -occs;
  push_stack (pivot);
  mark_lit (pivot);
  next = 0;
  expansion_cost_mark++;
  assert (expansion_cost_mark > 0);
  stretch = lit2stretch (pivot);

  if (!univ_mini && !in_innermost_ublock (pivot)) {
    return INT_MAX;
  }

  LOG ("checking expansion of %d in scope %d stretching to %d", 
       pivot, lit2order (pivot), stretch);
  while (next < nstack) {
    lit = stack[next++];
    assert (0 < lit && lit <= num_vars);
    v = vars + lit;
    for (sign = 0; sign <= 1; sign++) {
      occ = v->occs + sign;
      for (p = occ->first; p; p = p->next) {
	c = p->clause;
	assert (c->mark <= expansion_cost_mark);
	if (c->mark == expansion_cost_mark) continue;
	c->mark = expansion_cost_mark;
	res++;
	assert (res < INT_MAX);
	if (res > bound) {
	  LOG ("expansion of %d needs at least %d > %d clauses",
	       pivot, res, bound);
	  return INT_MAX;
	}
	for (q = c->nodes; (other = abs (q->lit)); q++) {
	  tmp = lit2var (other)->mark;
	  if (tmp) { assert (tmp == other); continue; }
	  tmp = lit2stretch (other);
	  if (tmp <= stretch) continue;
	  LOG ("expansion candidate %d depends on "
	       "variable %d in scope %d stretching to %d", 
	       pivot, other, lit2order (other), tmp);
	  if (universal (other)) {
	    assert (tmp > stretch);
	    LOG ("universal variable %d in scope %d stretching to %d "
	         "prohibits expansion of %d",
	         other, lit2order (other), tmp, pivot);
	    return INT_MAX;
	  }
	  push_stack (other);
	  mark_lit (other);
	}
      }
    }
  }
  assert (nstack > 0);
  LOG ("scope of universal %d has %d existential variables and %d clauses",
       pivot, nstack-1, res + occs);
  LOG ("expansion cost of %d would be at most %d clauses", pivot, res);
  return res;
}

static void expand_cost_clear (void) {
  while (nstack > 0) unmark_lit (stack[--nstack]);
  check_all_unmarked ();
}

static int expand_cost (int pivot, int bound) {
  int res = expand_cost_trav (pivot, bound);
  expand_cost_clear ();
  return res;
}

static void stretch_scopes (void) {
  Scope * p, * q, * next;
  for (p = outer_most_scope; p; p = p->inner) {
    q = p;
    while ((next = q->inner) && 
           (!next->free || next->type == p->type))
      q = next;
    while (p != q) {
      p->stretch = q->order;
      if (p->free)
	LOG ("scope %d actually stretches until scope %d",
	     p->order, q->order);
      else
	LOG ("empty scope %d also stretches until scope %d",
	     p->order, q->order);
      p = p->inner;
    }
  }
}

static void * fix_ptr (void * ptr, long delta) { 
  if (!ptr) return 0;
  return delta + (char*) ptr; 
}

static void fix_vars (long delta) {
  Var * v;
  Scope * s;
  for (s = outer_most_scope; s; s = s->inner) {
    v = s->first;
    if (!v) continue;
    s->first = fix_ptr (v, delta);
    s->last = fix_ptr (s->last, delta);
    for (v = s->first; v; v = v->next) {
      v->prev = fix_ptr (v->prev, delta);
      v->next = fix_ptr (v->next, delta);
    }
  }
}

static void enlarge_vars (int new_num_vars) {

  char * old_vars, * new_vars;
  int count, first_new_var;
  long delta;
  LOG ("enlarging variables from %d to %d", num_vars, new_num_vars);
  assert (num_vars <= new_num_vars);
  old_vars = (char*) vars;
  RSZ (vars, num_vars + 1, new_num_vars + 1);
  new_vars = (char*) vars;
  delta = new_vars - old_vars;
  if (delta) fix_vars (delta);
  dfsi -= num_vars;
  RSZ (dfsi, 2*num_vars + 1, 2*new_num_vars + 1);
  dfsi += new_num_vars;
  mindfsi -= num_vars;
  RSZ (mindfsi, 2*num_vars + 1, 2*new_num_vars + 1);
  mindfsi += new_num_vars;
  repr -= num_vars;
  RSZ (repr, 2*num_vars + 1, 2*new_num_vars + 1);
  repr += new_num_vars;
  RSZ (bwsigs, num_vars + 1, new_num_vars + 1);
  RSZ (fwsigs, num_vars + 1, new_num_vars + 1);
  RSZ (anchors, num_vars + 1, new_num_vars + 1);
  assert (next_on_trail == top_of_trail);
  count = top_of_trail - trail;
  RSZ (trail, num_vars + 1, new_num_vars + 1);
  top_of_trail = next_on_trail = trail + count;
  RSZ (schedule, num_vars + 1, new_num_vars + 1);
  first_new_var = num_vars + 1;
  remaining += new_num_vars - num_vars;
  num_vars = new_num_vars;
  init_variables (first_new_var);
}

static int expand_lit (int lit) {
  int res = lit2var (lit)->expcopy;
  if (!res) return lit;
  if (lit < 0) res = -res;
  return res;
}

static void expand_clause (Clause * c, int pivot) {
  int lit, other;
  int found_pivot = 0;

  Node * p;
  assert (c->mark == expansion_cost_mark);
  assert (!num_lits);
  if (!qrat_file) {
    for (p = c->nodes; (lit = p->lit); p++) {
      if (lit == pivot) continue;
      if (lit == -pivot) { num_lits = 0; return; }
      other = expand_lit (lit);
      push_literal (other);
    }

    if (trivial_clause ()) num_lits = 0 ;
    else add_clause ();
    return;

  } else {

    for (p = c->nodes; (lit = p->lit); p++) {
      if (lit == -pivot) { num_lits = 0; return; }
      if (lit == pivot) {  found_pivot = 1; continue; }
      other = expand_lit (lit);
      push_literal (other);
    }

      if (!found_pivot) {


        qrat_lit = -pivot;
        QRAT_TRACE_RATA_FROM_CLAUSE(c, 
            "expansion: aux clause with neg pivot");  
        qrat_lit = pivot;      
        QRAT_TRACE_RATA_FROM_STACK0("expansion: adding renamed clause");
 
        qrat_lit = 0;
        QRAT_TRACE_RATE_FROM_CLAUSE(c, "expansion: rm orig clause");  
      } else {
        
        qrat_lit = pivot;      
        QRAT_TRACE_RATA_FROM_STACK0("expansion: adding renamed clause");

        qrat_lit = pivot;
        QRAT_TRACE_RATE_FROM_CLAUSE(c, "expansion: rm orig clause");  

      }

      clause_stack_push ();
      num_lits = 0;
      if (!found_pivot) {
        for (p = c->nodes; (lit = p->lit); p++) {
          if (lit == pivot) {  found_pivot = 1; continue; }
          push_literal (lit);
        }
        assert (!found_pivot);
        clause_stack_push ();
        clause_stack[clause_stack_top-1][0] *= -1;
        num_lits = 0;
      }

  } 


}

static void expand (int pivot, int expected) {
  int ncopied, i, idx, first_new_var;
  #ifndef NDEBUG
  int max_cost;
  #endif
  Occ * occ;


  Clause * c, * last;
  Var * v;
  assert (isfree (pivot));
  LOG ("expanding %d with expected cost %d", pivot, expected);

  #ifndef NDEBUG
    max_cost = expand_cost_trav (pivot, expected + 1);
  #else 
    expand_cost_trav (pivot, expected + 1);
  #endif

  assert (nstack && stack[0] == pivot);
  #ifndef NDEBUG
  assert (max_cost == expected);
  LOG ("max cost for expansion %d", max_cost);
  #endif

  for (ncopied = 0; ncopied + 1 < nstack; ncopied++) {
    idx = stack[ncopied + 1];
    v = vars + idx;
    assert (!v->expcopy);
    v->expcopy = num_vars + ncopied + 1;
    LOG ("will copy %d to %d in expansion", idx, v->expcopy);
  }
  expand_cost_clear ();
  first_new_var = num_vars + 1;
  enlarge_vars (num_vars + ncopied);
  assert (inner_most_scope->type > 0);
  for (i = 0; i < ncopied; i++) {
    idx = stack[i + 1];
    v = vars + idx;
    add_var (v->expcopy, inner_most_scope);

    assert (!num_lits);
    qrat_lit = -v->expcopy;		//blocking!!
    push_literal (-v->expcopy);
    push_literal (pivot);
    push_literal (idx);
    QRAT_TRACE_RATA_FROM_STACK0("expansion: adding new variable");

    num_lits = 0;
    qrat_lit = v->expcopy;		// blocking!!
    push_literal (v->expcopy);
    push_literal (pivot);
    push_literal (-idx);
    QRAT_TRACE_RATA_FROM_STACK0("expansion: adding new variable");
    num_lits = 0;

  }
  assert (first_clause);
  last = last_clause;
  c = first_clause;
  do { 
    if (c->mark == expansion_cost_mark) 
      expand_clause (c, pivot);
    if (c == last) break;
    c = c->next;
  } while (!empty_clause);

  for (i = 0; i < ncopied; i++) {
    idx = stack[i + 1];
    v = vars + idx;
    assert (v->expcopy == num_vars - ncopied + i + 1);

    assert (!num_lits);
    qrat_lit = idx;
    push_literal (-v->expcopy);
    push_literal (pivot);
    push_literal (idx);
    QRAT_TRACE_RATE_FROM_STACK0("expansion: removing var definition");
    num_lits = 0;

    qrat_lit = -idx;
    push_literal (v->expcopy);
    push_literal (pivot);
    push_literal (-idx);
    QRAT_TRACE_RATE_FROM_STACK0("expansion: removing var definition");
    num_lits = 0;

    v->expcopy = 0;
  }


  expanded++;
  tag_lit (pivot, EXPANDED);
  assert (remaining > 0);
  remaining--;


  int deleted; 
  if (qrat_file) {
    for (i=0; i<clause_stack_top; i++) {
      int j;
      deleted = 0;
      assert(!num_lits);
      for (j = 1; j < abs(clause_stack[i][0])+1; j++) {
        push_literal(clause_stack[i][j]);
      }
      deleted = 0;
      if (clause_stack[i][0] < 0) {
          no_lookup = 1;
          QRAT_TRACE_EUR_FROM_STACK0(-pivot,"expansion: removal pivot neg");
          no_lookup = 0;
      } else {
        if (!lookup_without_lit(pivot) ) {
          QRAT_TRACE_EUR_FROM_STACK0(pivot,"expansion: removal pivot pos");
        } else {
          deleted = pivot;
	  qrat_lit = pivot; 
          QRAT_TRACE_RATE_FROM_STACK0("expansion: subs clause");
        }
        if (trivial_clause () || deleted) {
           num_lits = 0 ;
        }
        else {
          add_clause ();
        }
      }
      num_lits = 0;
      DELN(clause_stack[i], abs(clause_stack[i][0])+1);
    }


    clause_stack_top = 0;
    occ = lit2occ (-pivot);

    Node * p;
    Node * n;
    for (p = occ->first; p; p = p->next) {
      assert(p->lit == -pivot);
      assert (num_lits == 0);
      for (n=p->clause->nodes;n->lit;n++) {
        push_literal (n->lit);
      }

      if (!lookup_without_lit(-pivot) && !is_sat()) {
        QRAT_TRACE_EUR_FROM_CLAUSE(-pivot,p->clause,"expansion removal");
      }
      num_lits = 0; 
    }
  }

  LOG ("expanded %d remaining %d", pivot, remaining);
  assign (pivot);

  partial_expansion ();

  for (idx = first_new_var; idx <= num_vars; idx++)
    if (null_occurrences (idx)) zombie (idx);
}

static int try_expand (void) {
  int cost, lit, best, min, lim;
  int delta;
  double start, time;
  Scope * p;
  Var * v;

  if (!exp) return 0;

  start = seconds ();
  stretch_scopes ();
  min = lim = (axcess < INT_MAX) ? (axcess + 1) : INT_MAX;
  best = 0;
  for (p = inner_most_scope; p; p = p->outer) {
    if (p->type > 0) continue;
    for (v = p->first; v; v = v->next) {
      if (partial_assignment && v->scope->order == assigned_scope) continue;
      if (v->tag != FREE) continue;
      lit = v - vars;
      cost = expand_cost (lit, min);
      if (cost == INT_MAX) continue;
      if (cost >= min) continue;
      best = lit;
      min = cost;
    }
  }
  assert (min == lim || best);
  LOG ("minimial expansion cost is at most %d expanding %d", min, best);
  time = seconds () - start;
  expTime += time;
  if (min > axcess) {
    msg ("minimial expansion cost limit of %d exceeded in %.1f seconds",
         axcess, time);
    return 0;
  }
  msg ("found minimial expansion cost of %d in %.1f seconds", min, time);
  delta = num_clauses;
  expand (best, min);
  flush (0);
  delta -= num_clauses;
  LOG ("expansion of %d removed %d clauses", best, delta);
  expTime += (seconds() - start);
  return 1;
}

/* splitting a clause of length C into N clauses of at most length L 
 * by introducing V = N-1 variables:
 *                                                               C/L  N
 *                                                               
 * (1 2 3 4)     -> (1 2 -5)(5 3 4)                              4/3  2
 * (1 2 3 4 5)   -> (1 2 -6)(6 3 -7)(7 4 5)                      5/3  3
 * (1 2 3 4 5 6) -> (1 2 -7)(7 3 -8)(8 4 -9)(9 5 6)              6/3  4
 *                                                               
 *                                                               C/3  C-2
 *                                                         
 * (1 2 3 4 5)         -> (1 2 3 -6)(6 4 5)                      5/4  2
 * (1 2 3 4 5 6)       -> (1 2 3 -7)(7 4 5 6)                    6/4  2
 * (1 2 3 4 5 6 7)     -> (1 2 3 -8)(8 4 5 -9)(9 6 7)            7/4  3
 * (1 2 3 4 5 6 7 8)   -> (1 2 3 -9)(9 4 5 -10)(10 6 7 8)        8/4  3
 * (1 2 3 4 5 6 7 8 9) -> (1 2 3 -a)(a 4 5 -b)(b 6 7 -c)(c 8 9)  9/4  4 
 *
 *                                                               C/4  (C-1)/2
 *
 * (1 2 3 4 5 6)       -> (1 2 3 4 -a)(a 5 6)                    6/5  2
 * (1 2 3 4 5 6 7)     -> (1 2 3 4 -a)(a 5 6 7)                  7/5  2
 * (1 2 3 4 5 6 7 8)   -> (1 2 3 4 -a)(a 5 6 7 8)                8/5  2
 * (1 2 3 4 5 6 7 8 9) -> (1 2 3 4 -a)(a 5 6 7 b)(-b 8 9)        9/5  3
 *
 * (1 2 3 4 5 6 7 8 9 10) ->
 *   (1 2 3 4 -a)(a 5 6 7 b)(b 8 9 10)                          10/5  3
 *
 * (1 2 3 4 5 6 7 8 9 10 11) ->
 *   (1 2 3 4 -a)(a 5 6 7 -b)(b 8 9 10 11)                      11/5  3
 *
 * (1 2 3 4 5 6 7 8 9 10 11 12) ->
 *   (1 2 3 4 -a)(a 5 6 7 -b)(b 8 9 10 -c)(c 11 12)             12/5  4
 *
 * (1 2 3 4 5 6 7 8 9 10 11 12 13) ->
 *   (1 2 3 4 -a)(a 5 6 7 -b)(b 8 9 10 -c)(c 11 12 13)          13/5  4
 *
 * (1 2 3 4 5 6 7 8 9 10 11 12 13 14) ->
 *   (1 2 3 4 -a)(a 5 6 7 -b)(b 8 9 10 -c)(c 11 12 13 14)       14/5  4
 *
 *                                                               C/5  C/3
 *
 * (1 2 3 4 5 6 7) -> (1 2 3 4 5 -a) (a 6 7)                     7/6  2
 * (1 2 3 4 5 6 7 8) -> (1 2 3 4 5 -a) (a 6 7 8)                 8/6  2
 * (1 2 3 4 5 6 7 8 9) -> (1 2 3 4 5 -a) (a 6 7 8 9)             9/6  2
 * (1 2 3 4 5 6 7 8 9 10) -> (1 2 3 4 5 -a) (a 6 7 8 9 10)      10/6  2
 *
 * (1 2 3 4 5 6 7 8 9 10 11) ->
 *   (1 2 3 4 5 -a)(a 6 7 8 9 -b)(b 10 11)                      11/6  3
 *
 * (1 2 3 4 5 6 7 8 9 10 11 12) ->
 *   (1 2 3 4 5 -a)(a 6 7 8 9 -b)(b 10 11 12)                   12/6  3
 *
 * (1 2 3 4 5 6 7 8 9 10 11 12 13) ->
 *   (1 2 3 4 5 -a)(a 6 7 8 9 -b)(b 10 11 12 13)                13/6  3
 *
 * (1 2 3 4 5 6 7 8 9 10 11 12 13 14) ->
 *   (1 2 3 4 5 -a)(a 6 7 8 9 -b)(b 10 11 12 13 14)             14/6  3
 *
 * (1 2 3 4 5 6 7 8 9 10 11 12 13 14 15) ->
 *   (1 2 3 4 5 -a)(a 6 7 8 9 -b)(b 10 11 12 13 -c)(c 14 15)    15/6  4
 *
 *                                                               C/6  (C+1)/4
 */

static int split_clause (Clause * c, int next) {
  int res = next, i, size;
  Node * p, * q;
  LOGCLAUSE (c, "splitting length %d clause", c->size);
  size = c->size;
  assert (size > splitlim);
  assert (!num_lits);
  p = c->nodes;
  for (i = 0; i < splitlim - 1; i++) push_literal (p++->lit);
  push_literal (-res);
  qrat_lit = -res;
  QRAT_TRACE_RATA_FROM_STACK0("splitting");
  qrat_lit = res;
  QRAT_TRACE_RATA_FROM_CLAUSENODES(p,"splitting");
  QRAT_TRACE_RATE_FROM_CLAUSE(c,"splitting");
  assert (!trivial_clause ());
  add_clause ();
  size -= splitlim - 1;
  q = p;
  while (size > splitlim - 1) {
    assert (!num_lits);
    push_literal (res);
    for (i = 0; i < splitlim - 2; i++) push_literal (p++->lit);
    push_literal (-++res);
    qrat_lit = -res;
    QRAT_TRACE_RATA_FROM_STACK0("splitting");
    qrat_lit = res;
    QRAT_TRACE_RATA_FROM_CLAUSENODES(p,"splitting");
    qrat_lit = (res-1);
    QRAT_TRACE_RATE_FROM_CLAUSENODES(q,"splitting");
    assert (!trivial_clause ());
    add_clause ();
    size -= splitlim - 2;
    q = p;
  }
  assert (2 <= size && size <= splitlim -1);
  push_literal (res++);
  while (size-- > 0) push_literal (p++->lit);
  assert (!p->lit);
  assert (!trivial_clause ());
  add_clause ();
  return res;
}

static void split (void) {
  int sumvars, sumclauses, splitted, size, maxsize, vars, clauses;
  double start = seconds();

  Clause * p, * next_clause;
  int idx, next_idx;
  if (!first_clause) return;
  sumclauses = sumvars = splitted = 0;
  maxsize = -1;
  for (p = first_clause; p; p = p->next) {
    size = p->size;
    if (size > maxsize) maxsize = size;
    if (size <= splitlim) continue;
    clauses = 1;
    size -= splitlim - 1;
    vars = 1;
    while (size > splitlim - 1) {
      size -= splitlim - 2;
      clauses++;
      vars++;
    }
    assert (2 <= size && size < splitlim);
    clauses++;
    assert (vars == clauses - 1);
    sumclauses += clauses;
    sumvars += vars;
    splitted++;
    LOGCLAUSE (p,
               "using %d variables and %d new clauses to split clause",
               vars, clauses); 
  } 
  if (!splitted) {
    assert (0 <= maxsize && maxsize <= splitlim);
    msg ("largest clause size is %d so no need to split any clause", maxsize);
    return;
  }
  msg ("splitting %d clauses using %d variables into %d clauses",
       splitted, sumvars, sumclauses);
  next_idx = num_vars + 1;
  enlarge_vars (num_vars + sumvars);
  for (idx = next_idx; idx <= num_vars; idx++)
    add_quantifier (idx);
  for (p = first_clause; p; p = next_clause) {
    next_clause = p->next;
    if (p->size <= splitlim) continue;
    next_idx = split_clause (p, next_idx);
    delete_clause (p);
  }
  assert (num_vars + 1 == next_idx);
  flush (0);

  splitTime += (seconds() - start);
}

static void map_vars (void) {
  Var * v;
  mapped = 0;
  assert (trail_flushed ());
  for (v = vars + 1; v <= vars + num_vars; v++) {
    if (v->tag != FREE) continue;
    v->mapped = ++mapped;
    LOG ("mapped %d to %d", (int)(long)(v - vars), mapped);
  }
  if (empty_clause) assert (!mapped), remaining = 0;
  else assert (mapped == remaining);
}

static void print_clause (Clause * c, FILE * file) {
  Node * p;
  for (p = c->nodes; p->lit; p++)
    fprintf (file, "%d ", map_lit (p->lit));
  fputs ("0\n", file);
}

static void print_clauses (FILE * file) {
  Clause * p;
  for (p = first_clause; p; p = p->next)
    print_clause (p, file);
}

static int print_scope (Scope * s, FILE * file, int pscope) {
  Var * p;

  if (!pscope || (pscope != s->type)) {
    if (pscope) fputs (" 0\n", file);
    fputc (s->type < 0 ? 'a' : 'e', file);
  }
  for (p = s->first; p; p = p->next) {
    if (p->tag != FREE) continue;
    fprintf (file, " %d", map_lit (var2lit (p)));
  }
  return s->type;
}

static int empty_scope (Scope * s) {
  int res = 1;
  Var * p;
  for (p = s->first; res && p; p = p->next)
    if (p->tag == FREE)
      res = 0;
  assert (res == !s->free);
  return res;
}

static int propositional (void) {
  Scope * p;
  for (p = outer_most_scope; p; p = p->inner)
    if (p->type < 0 && !empty_scope (p)) return 0;
  return 1;
}

static void print_scopes (FILE * file) {
  int type = 0; 
  Scope * p, * first = 0;
  if (propositional () && !quantifyall) return;
  for (p = outer_most_scope; p; p = p->inner) {
    if (!quantifyall && !first && p->type > 0) continue;
    if (empty_scope (p)) { continue; }
    first = p;
    type = print_scope (p, file, type);
  }
  if (type) fputs (" 0\n", file);
}

static void print (FILE * file) {
  fprintf (file, "p cnf %d %d\n", mapped, num_clauses);
  print_scopes (file);
  print_clauses (file);
}

static void release_clauses (void) {
  Clause * p, * next;
  size_t bytes;
  for (p = first_clause; p; p = next) {
    next = p->next;
    bytes = bytes_clause (p->size);
    DEC (bytes);
    free (p);
  }
}

static void release_scopes (void) {
  Scope * p, * next;
  for (p = outer_most_scope; p; p = next) {
    next = p->inner;
    DEL (p);
  }
}

static void release (void) {
  release_clauses ();
  release_scopes ();
  DELN (line, szline);
  szline = 0;
  line = NULL;
  DELN (lits, size_lits);
  size_lits = num_lits = 0;
  lits = NULL;
  DELN (stack, szstack);
  szstack = 0;
  DELN (clause_stack, clause_stack_size);
  clause_stack_size = 0;
  stack = NULL;
  DELN (aux, szaux);
  szaux = 0;
  aux = NULL;
  DELN (vars, num_vars + 1);
  vars = NULL;
  dfsi -= num_vars;
  DELN (dfsi, 2*num_vars+1);
  dfsi = NULL;
  mindfsi -= num_vars;
  DELN (mindfsi, 2*num_vars+1);
  mindfsi = NULL;
  DELN (subst_vals, orig_num_vars+1);
  subst_vals = NULL;
  repr -= num_vars;
  DELN (repr, 2*num_vars+1);
  repr = NULL;
  DELN (bwsigs, num_vars + 1);
  bwsigs = NULL;
  DELN (fwsigs, num_vars + 1);
  fwsigs = NULL;
  DELN (anchors, num_vars + 1);
  anchors = NULL;
  DELN (trail, num_vars);
  trail = NULL;
  DELN (schedule, num_vars);
  schedule = NULL;
  num_vars = 0;


  assert (getenv ("LEAK") || current_bytes == 0);
}

static double percent (double a, double b) {
  return b ? (100.0 * a / b) : 0.0;
}

static double average (double a, double b) {
  return b ? a / b : 0.0;
}

static const char * USAGE =
"usage: bloqqer [<option> ...] [<in> [<out>]]\n"
"\n"
"input and output files are specified as (use '-' for default)\n"
"\n"
"  <in>                input QDIMACS file (default <stdin>)\n"
"  <out>               output QDIMACS file (default <stdout>)\n"
"\n"
"  -n                  no output, see also '--output' below\n"
"\n"
"For all of the following options '--<opt>=<v>' there also exist an\n"
"'--no-<opt>' and '--<opt>' version.  The former sets the option value\n"
"to zero and the later increments the current / default value.  They\n"
"can also be embedded in comments before the 'p cnf' header in '<in>'.\n"
"\n"
;

static void init_opts (void) {
  Opt * p;
  for (p = opts; p->name; p++) {
    assert (p->low <= p->def && p->def <= p->high);
    *p->valptr = p->def;
  }
  if (bound >= 0) force_bound ();
}

static void list_usage (void) {

  #ifdef COMP 
    fputs ("usage: bloqqer <file> <timeout>\n",stdout);
    return;
  #endif

  int len, tmp, i;
  char * buf;
  Opt * p;
  StrOpt * q;
  fputs (USAGE, stdout);
  len = 0;
  for (p = opts; p->name; p++) {
    tmp = strlen (p->name) + 2;
    if (p->inc) tmp += 3;
    if (tmp > len) len = tmp;
  }
  for (q = str_opts; q->name; q++) {
    tmp = strlen (q->name) + 2;
    if (tmp > len) len = tmp;
  }
  len += 8;
  NEWN (buf, len + 1);
  for (p = opts; p->name; p++) {
    if (p->inc) sprintf (buf, "-%c | --%s=<v>", p->inc, p->name);
    else sprintf (buf, "     --%s=<v>", p->name);
    assert (strlen (buf) <= len);
    fputs (buf, stdout);
    for (i = strlen (buf); i < len; i++) fputc (' ', stdout);
    fputs (p->description, stdout);
    printf (" (default %d)\n", p->def);
  }
  for (q = str_opts; q->name; q++) {
    sprintf (buf, "     --%s=<f>", q->name);
    assert (strlen (buf) <= len);
    fputs (buf, stdout);
    for (i = strlen (buf); i < len; i++) fputc (' ', stdout);
    fputs (q->description, stdout);
    printf (" (output <f>)\n");
  }
  DELN (buf, len + 1);
}

static void list_opts_ranges (void) {
  Opt * p = opts;
  while (strcmp (p->name, "range")) p++;
  for (p++; p->name; p++)
    printf ("%s %d %d %d\n", p->name, p->def, p->low, p->high);
}

static void list_opts_defaults (void) {
  Opt * p;
  for (p = opts; p->name; p++)
    printf ("%s %d\n", p->name, p->def);
}

static void list_opts_defaults_in_embedded_format (void) {
  Opt * p = opts;
  while (strcmp (p->name, "range")) p++;
  for (p++; p->name; p++)
    printf ("c --%s=%d\n", p->name, p->def);
}



static void stats (void) {
  msg ("");
  msg ("[final statistics follow]");
  msg ("");
  msg ("%d units %.0f%%", units, percent (units, num_vars));
  msg ("%d zombie variables %.0f%%", zombies, percent (zombies, num_vars));
  msg ("%d eliminated variables %.0f%%", 
       eliminated, percent (eliminated, num_vars));
  msg ("%d expanded variables %.0f%%", 
       expanded, percent (expanded, num_vars));
  msg ("%d substituted variables %.0f%%", 
       substituted, percent (substituted, num_vars));
  msg ("%d existential pure literals %.0f%%", 
       unets, percent (unets, num_vars));
  msg ("%d universal pure literals %.0f%%", 
       unates, percent (unates, num_vars));
  msg ("");
  msg ("%d pushed variables %.2f per variable", 
       pushed_vars, average (pushed_vars, num_vars));
  msg ("%d added clauses %.2f per original clause",
       added_clauses, average (added_clauses, orig_clauses));
  msg ("%d enqueued clauses %.2f per added clause", 
       enqueued_clauses, average (enqueued_clauses, added_clauses));
  msg ("");
  msg ("%d subsumed clauses (%.0f%% of all added clauses)", 
       subsumed_clauses, percent (subsumed_clauses, added_clauses));
  msg ("%d backward subsumed (%.0f%% of all subsumed clauses)",
       backward_subsumed_clauses,
       percent (backward_subsumed_clauses, subsumed_clauses));
  msg ("%d forward subsumed (%.0f%% of all subsumed clauses)",
       forward_subsumed_clauses,
       percent (forward_subsumed_clauses, subsumed_clauses));
  msg ("");
  msg ("%d strengthened clauses (%.0f%% of all added clauses)", 
       strengthened_clauses, percent (strengthened_clauses, added_clauses));
  msg ("%d backward strengthened (%.0f%% of all strengthened clauses)",
       backward_strengthened_clauses,
       percent (backward_strengthened_clauses, strengthened_clauses));
  msg ("%d forward strengthened (%.0f%% of all strengthened clauses)",
       forward_strengthened_clauses,
       percent (forward_strengthened_clauses, strengthened_clauses));
  msg ("");
  msg ("%lld fwsig1 lookups with %lld hits (%.0f%% hit rate)",
       fw.sig1.lookups, fw.sig1.hits, percent (fw.sig1.hits, fw.sig1.lookups));
  msg ("%lld fwsig2 lookups with %lld hits (%.0f%% hit rate)",
       fw.sig2.lookups, fw.sig2.hits, percent (fw.sig2.hits, fw.sig2.lookups));
  msg ("%lld bwsig1 lookups with %lld hits (%.0f%% hit rate)",
       bw.sig1.lookups, bw.sig1.hits, percent (bw.sig1.hits, bw.sig1.lookups));
  msg ("%lld bwsig2 lookups with %lld hits (%.0f%% hit rate)",
       bw.sig2.lookups, bw.sig2.hits, percent (bw.sig2.hits, bw.sig2.lookups));
  msg ("");
  msg ("%d equivalence reasoning rounds", eqrounds);
  msg ("%lld hidden %lld covered literal additions", hlas, clas);
  msg ("");
  msg ("%d blocked literals", 
       blocked_lits);
  msg ("%d blocked clauses %.0f%% of all added clauses", 
       blocked_clauses, percent (blocked_clauses, added_clauses));
  msg ("%d not blocked clauses because pivot in outermost scope",outermost_blocked);
  msg ("%d hidden tautologies %.0f%% of all added clauses", 
       hidden_tautologies, percent (hidden_tautologies, added_clauses));
  msg ("%d asymmetric blocked literals", 
       hidden_blocked_literals);
  msg ("%d hidden blocked clauses %.0f%% of all added clauses", 
       hidden_blocked_clauses,
       percent (hidden_blocked_clauses, added_clauses));
  msg ("%d non-strict variable eliminations %.0f%%",
       nonstrictves, percent (nonstrictves, eliminated));
  msg ("");
  msg ("%d remaining variables %.0f%% out of %d", 
       remaining, percent (remaining, num_vars), num_vars);
  msg ("%d remaining clauses %.0f%% out of %d", 
       num_clauses, percent (num_clauses, orig_clauses), orig_clauses);
  msg ("");
  msg ("%.3f seconds, %.1f MB", seconds (), max_bytes /(double)(1<<20));
  msg ("parse time: %.3f", parseTime);
  msg ("hte time: %.3f", hteTime);  
  msg ("bce time: %.3f", bceTime);  
  msg ("eq time: %.3f", eqTime);  
  msg ("ve time: %.3f", veTime);  
  msg ("cce time: %.3f", cceTime);  
  msg ("hbce time: %.3f", hbceTime);  
  msg ("split time: %.3f", splitTime);  
  msg ("exp time: %.3f", expTime);  
  msg ("subsumption time: %.3f", subsTime);  
  msg ("strength time: %.3f", strengthTime);  
  msg ("univ. red. time: %.3f", univredTime);  
  msg ("triv. time: %.3f", trivclauseTime);  
  msg ("pure time: %.3f", pureTime);  
  msg ("elim time: %.3f", elimTime);  
  msg ("flush time: %.3f", flushTime);  
  double sum = hteTime+bceTime+eqTime+veTime+hbceTime+splitTime+expTime+strengthTime+subsTime+univredTime+trivclauseTime;
  msg ("total time: %.3f", sum);
}


#ifdef SOLVER

static void addPrefix (QDPLL *depqbf) {
  Var *v;
  Scope *s;

  for (s = outer_most_scope; s; s = s->inner) {

    qdpll_new_scope (depqbf,
      (s->type < 0 ? QDPLL_QTYPE_FORALL : QDPLL_QTYPE_EXISTS));

    for (v = s->first; v; v = v->next) {
      if (v->tag != FREE) continue;
      qdpll_add(depqbf, map_lit(var2lit(v)));
    }

    qdpll_add(depqbf, 0);

  }

}


static void addMatrix(QDPLL *depqbf) {
  Clause *p;
  Node *n;

  for (p = first_clause; p; p = p->next) {
    for (n = p->nodes; n->lit; n++) {
      qdpll_add(depqbf, map_lit(n->lit));
    }
    qdpll_add(depqbf, 0);
  }
}


static QDPLL * init_depqbf () {
  QDPLL *depqbf = qdpll_create();
  qdpll_configure(depqbf, "--dep-man=qdag"); 

  addPrefix(depqbf);
  addMatrix(depqbf);

  return depqbf;
}


void bloqqer_assume (int lit) {

  if (!qdpll) {

    qdpll = init_depqbf ();
  }
  if ((lit <= num_vars) && (lit2var(lit)->tag == FREE))
  qdpll_assume (qdpll, lit);

}

void bloqqer_reset_assumptions () {
  if (qdpll) qdpll_reset(qdpll);
}


static int solve () {
  int res; 
  Var * v;
  int i = 0, tmp;

  if (partial_assignment) {

    for (i = 0; i <= num_vars; i++) {
      if (vars[i].tag == ZOMBIE) vars[i].fixed = i;
    }

  }


  msg("solving with DepQBF"); 



  if (!qdpll) qdpll = init_depqbf ();
   
  res = qdpll_sat(qdpll);

  if (partial_assignment) {
    for (i = 1; i < num_vars; i++) {
      v = vars + i;
      if ((v->scope->order == 0) && (v->tag == FREE)) {
        tmp = qdpll_get_value(qdpll, i);
        v->fixed = tmp*i;
	v->tag = SOLVING;
      }
    }
  }


  switch(res) {
    case 10: 	msg("SAT");
		break;
    case 20:	msg("UNSAT");
		break;
    default: 	msg("solving aborted");
		break;
  }
  return res;

}

static void print_part_assignment (int scope) {
  int i; 
  Var v;
  if (!partial_assignment) return;


  for (i = 1; i <= num_vars; i++) {
    v = vars[i];
    if (v.scope->order == scope)  {
	fprintf(stderr,"%d %d\n",v.fixed,bloqqer_getvalue(i));
    }
  }

}

#endif




/******* bloqqer API *******/


void bloqqer_parse (char * iname) {
  FILE * ifile; 

  init_opts ();

  ifile = fopen (iname, "r");
  if (!ifile) {
    msg ("can not read '%s'", iname);
    return;
  }

  parse(ifile, iname);

  fclose(ifile);
  
  implicit_scopes_inited = 1; 

}

void bloqqer_stats () {
  stats ();
}

void bloqqer_init (int m, int n) {
  assert (m > 0);
  assert (n > 0);
  int i; 

  init_opts ();
  keep = 1;

  set_signal_handlers(); 

  remaining = num_vars = m;
  remaining_clauses_to_parse = n;


  NEWN (vars, num_vars + 1);
  if (num_vars) init_variables (1);
  NEWN (dfsi, 2*num_vars+1);
  dfsi += num_vars;
  NEWN (mindfsi, 2*num_vars+1);
  mindfsi += num_vars;
  NEWN (repr, 2*num_vars+1);
  repr += num_vars;
  orig_num_vars = num_vars;
  NEWN (subst_vals, num_vars+1);
  for (i = 0; i < num_vars+1; i++) {
    subst_vals [i] = i;
  }
  NEWN (fwsigs, num_vars + 1);
  NEWN (bwsigs, num_vars + 1);
  NEWN (anchors, num_vars + 1);
  NEWN (trail, num_vars);

  top_of_trail = next_on_trail = trail;
  NEWN (schedule, num_vars);
  assert (!size_schedule);

}


void bloqqer_decl_var ( int var ) {
 if (implicit_scopes_inited) {
   msg ("clauses have already been added");
   return;
 }

 if (var) {

    if (abs(var) > num_vars) {
      msg ("maximum variable index exceeded");
      return;
    } 
    if (lit2scope (var)) {
      msg ("variable %d quantified twice", abs(var));
      return;
    }
    add_quantifier (var);
    if (var > 0) existential_vars++; else universal_vars++;
  }
}


void bloqqer_add ( int lit ) {
  if (!implicit_scopes_inited) {
    implicit_scopes_inited = 1;
    init_implicit_scope ();
  }

  if (!lit) remaining_clauses_to_parse--;
  if (lit) push_literal (lit); 
  else {
    if (!trivial_clause ()) {
      add_clause ();
    }
    num_lits = 0;
  }
 
}




int bloqqer_preprocess () {
  int res;

  if (!implicit_scopes_inited) {
    msg ("no clauses given");
    return 10;
  }


  flush_vars ();
  for (;;) {
    flush (1);
    split ();
    if (empty_clause || !num_clauses) break;
    if (eqres (1)) flush (0);
    if (empty_clause || !num_clauses) break;
    elim ();
    if (verbose) log_pruned_scopes ();
    if (empty_clause || !num_clauses) break;
    if (propositional ()) break;
    if (!try_expand ()) break;
  }
  if (empty_clause) { res = 20; msg ("definitely UNSATISFIABLE"); }
  else if (!num_clauses) { res = 10; msg ("definitely SATISFIABLE"); }
  else { res = 0; msg ("unknown status"); }
  split ();
  if (keep) remaining = num_vars; else map_vars ();
 
  return res;
}


VarValue bloqqer_getvalue (int v) {
  int pol = 1;
  VarValue val;

  assert (v > 0);

  if (!partial_assignment) return UNKN;
  
  Var w = vars [v];
  int tmp;
  if (w.scope->order != assigned_scope) return UNKN;

  assert (w.tag != EXPANDED);
  assert (w.tag != ELIMINATED);

  if (w.tag == FREE) return UNKN;
  if (w.tag == ZOMBIE) return POS; 
  if (w.tag == SUBSTITUTED) {
    tmp = subst_vals[abs(v)];
    if (tmp < 0) pol = pol * -1;
    while ((vars[abs(tmp)].tag == SUBSTITUTED) && 
	   (abs(subst_vals [abs(tmp)]) != abs(tmp))) {
      tmp = subst_vals [abs(tmp)];
      if (tmp < 0) pol = pol * -1;
    }
    val =  bloqqer_getvalue (abs(tmp));
    if (pol > 0) return val;
    if (val == POS) return NEG;
    if (val == NEG) return POS;
    return val;
  }
   
  if (w.fixed > 0) return POS; else return NEG; 

}


void bloqqer_reset () {
  release ();
  outermost_blocked = 0;
  blocked_clauses = 0;
  blocked_lits = 0;
  mapped = 0;
  num_vars = 0;
  size_schedule = 0;
  implicit_scopes_inited = 0;
  inner_most_scope = outer_most_scope = NULL;
  last_clause = first_clause = NULL;
  queue = NULL; 
  universal_vars = 0; 
  existential_vars = 0;
  implicit_vars = 0;
  nstack  = 0;
  naux = 0;
  current_bytes = 0;
  max_bytes = 0;
  empty_clause = NULL;
  embedded_options = 0;
  command_line_options = 0;
  added_clauses = 0; 
  added_binary_clauses = 0; 
  enqueued_clauses = 0; 
  pushed_vars = 0;
  subsumed_clauses = 0; 
  strengthened_clauses = 0;
  forward_subsumed_clauses = 0; 
  forward_strengthened_clauses = 0;
  backward_subsumed_clauses = 0; 
  backward_strengthened_clauses = 0;
  blocked_clauses = 0; 
  orig_clauses = 0; 
  num_clauses = 0; 
  hidden_tautologies = 0;
  units = 0; 
  unates = 0; 
  unets = 0; 
  zombies = 0; 
  eliminated = 0; 
  remaining = 0; 
  mapped = 0;
  substituted = 0; 
  eqrounds = 0; 
  nonstrictves = 0; 
  hidden_blocked_clauses = 0;  
  hidden_blocked_literals = 0;  
  added_binary_clauses_at_last_eqround = 0;

}

void bloqqer_release () {
  bloqqer_reset ();
}





int bloqqer_solve () {

 int res = 0;
#ifdef SOLVER 
  if (depqbf_on) {
    res = solve();
  }
#endif

return res;


}


void bloqqer_print () {
  print (stdout);
}


void bloqqer_reset_lit_iterator () {

 cl_iterator = first_clause;
 lit_iterator = cl_iterator->nodes;
}


int bloqqer_lit_iterator_next () {
  int lit; 

  if (!cl_iterator) return 0;
  if (!lit_iterator->lit) {

    cl_iterator = cl_iterator->next;
    if (!cl_iterator) return 0;
    lit_iterator = cl_iterator->nodes;   

  }

  lit = lit_iterator->lit;
  lit_iterator++;

  return lit;  

}


void bloqqer_set_option(char * arg) {
  if (parse_opt (arg)) {
    if (help) { list_usage (); }
    if (range) { list_opts_ranges (); } 
    if (defaults) { list_opts_defaults (); }
    if (embedded) { list_opts_defaults_in_embedded_format (); }
    command_line_options++;
    msg ("option: %s", arg);
  } else {
    msg ("invalid option: %s", arg);
  }
}


int bloqqer_set_option_val (const char * opt, int val) {
  Opt * p;
  int len = strlen (opt);

  for (p = opts; p->name; p++) {
    if (strlen (p->name) == len && !strncmp (opt, p->name, len))
      break;
  }
  if (!p->name) return 0;
  if (val < p->low) return 0; 
  if (val > p->high) return 0;
  if (!strcmp (p->name, "bound")) {
    assert (p->low == -1);
    if (val == -1) force_no_bound ();
    else force_bound ();
  }
  p->def = val; 


  return 1; 
}


Opt * current_option = opts; 

void * bloqqer_next_opt (const char **nameptr,
                        int *valptr, int *minptr, int *maxptr) {
  Opt * opt = current_option, * res = opt + 1;
  if (!opt->name) return 0;
  current_option++;
  if (nameptr) *nameptr = opt->name;
  if (valptr) *valptr = opt->def;
  if (minptr) *minptr = opt->low;
  if (maxptr) *maxptr = opt->high;
  return res;

}

void bloqqer_reset_option_iterator () {
  current_option = opts;
}


#ifndef LIBBLOQQER
int main (int argc, char ** argv) {
  int ifclose, ipclose, oclose;
  FILE * ifile, * ofile;
  char * iname, * oname;
  const char * perr;
  int i, res;

  iname = oname = NULL;
  ofile = NULL;
  ipclose = 0;
  oclose = 0;
  init_opts ();
  #ifdef COMP
    if (argc != 3) { list_usage(); exit(0); }
    iname = argv[1];
    timelimit = atoi(argv[2]);
    output = 0;
  #else

  for (i = 1; i < argc; i++) if (!strcmp (argv[i], "-v")) verbose = 1;
  msg ("Bloqqer QBF Preprocessor");
  msg ("Version %s %s", blqr_version (), blqr_id ());
  msg ("Copyright (C) 2010 by Armin Biere JKU Linz");
  msg ("%s", blqr_cflags());
  for (i = 1; i < argc; i++) {
    if (parse_opt (argv[i])) {
      if (help) { list_usage (); exit (0); }
      if (range) { list_opts_ranges (); exit (0); }
      if (defaults) { list_opts_defaults (); exit (0); }
      if (embedded) { list_opts_defaults_in_embedded_format (); exit (0); }
      command_line_options++;
      msg ("command line option: %s", argv[i]);
    } else if (argv[i][0] == '-' && argv[i][1]) 
      die ("invalid command line option '%s' (try '-h')", argv[i]);
    else if (oname) die ("too many file names (try '-h')");
    else if (iname) oname = argv[i], msg ("output: %s", oname);
    else iname = argv[i], msg ("input: %s", iname);
  }
  if (oname && !output) die ("both '-n' and '<out>' specified");

  #endif

  if (iname && strcmp (iname, "-")) {
    if ((i = strlen (iname)) >= 3 && !strcmp (iname + i - 3, ".gz")) {
      char * cmd;
      NEWN (cmd, i + 30);
      sprintf (cmd, "gunzip -c %s", iname);
      ifile = popen (cmd, "r");
      DELN (cmd, i + 30);
      ipclose = 1;
    } else {
      ifile = fopen (iname, "r");
      ifclose = 1;
    }
    if (!ifile) die ("can not read '%s'", iname);
  } else {
    ifile = stdin;
    iname = "<stdin>";
  }
  terminal = isatty (1);
  msg ("finished parsing %d command line options", command_line_options);

  if (qrat_trace) {
    qrat_file = fopen (qrat_trace, "w");
  }

  FILE * ifile2 = NULL;
  if (qrat_file) {
    ifile2 = fopen (iname,"r");
  }
  parsing = 1;
  perr = parse (ifile, iname);
  parsing = 0;  

  if (qrat_file) {
    fclose (ifile2);
  }

  if (perr) {
    stop_progress ();
    fprintf (stderr, "%s:%d: %s\n", iname, lineno, perr);
    fflush (stderr);
    exit (1);
  }
  if (ifclose) fclose (ifile);
  if (ipclose) pclose (ifile);

  if (timelimit) {

    msg("setting time limit of %d seconds\n", timelimit);
    set_signal_handlers();
    alarm(timelimit);
    
  } 

  flush_vars ();
  for (;;) {
    flush (1);
    split ();
    if (empty_clause || !num_clauses) break;
    if (eqres (1)) flush (0);
    if (empty_clause || !num_clauses) break;
    elim ();
    if (verbose) log_pruned_scopes ();
    if (empty_clause || !num_clauses) break;
    if (propositional ()) break;
    flush (1);
    if (!try_expand ()) break;
  }
  flush_trail ();
  if (empty_clause) { res = 20; msg ("definitely UNSATISFIABLE"); }
  else if (!num_clauses) { res = 10; msg ("definitely SATISFIABLE"); }
  else { res = 0; msg ("unknown status"); }
  split ();
  if (keep) remaining = num_vars; else map_vars ();


  if (oname && strcmp (oname, "-")) {
    assert (output);
    ofile = fopen (oname, "w");
    if (!ofile) die ("can not write '%s'", oname);
    oclose = 1;
  } else if (output) {
    ofile = stdout;
    oname = "<stdout>";
  }
  if (propositional ()) msg ("result is propositional");
  else msg ("result still contains universal quantifiers");
  if (output) print (ofile);

#ifdef SOLVER 
  if (depqbf_on) {
    res = solve();
    if (partial_assignment) {
      print_part_assignment(assigned_scope);
    }  
  } 
#endif
  if (oclose) fclose (ofile);
  if (qrat_trace) fclose (qrat_file);
  release ();
  stats ();
  return res;
}


#ifndef NDEBUG
void dump (void) { print (stdout); }
void dump_clause (Clause * c) { print_clause (c, stdout); }
void dump_scope (Scope * s) { print_scope (s, stdout, 0); }
#endif
#endif
