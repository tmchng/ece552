
#include <limits.h>
#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>

#include "host.h"
#include "misc.h"
#include "machine.h"
#include "regs.h"
#include "memory.h"
#include "loader.h"
#include "syscall.h"
#include "dlite.h"
#include "options.h"
#include "stats.h"
#include "sim.h"
#include "decode.def"

#include "instr.h"

/* PARAMETERS OF THE TOMASULO'S ALGORITHM */

#define INSTR_QUEUE_SIZE         10

#define RESERV_INT_SIZE    4
#define RESERV_FP_SIZE     2
#define FU_INT_SIZE        2
#define FU_FP_SIZE         1

#define FU_INT_LATENCY     4
#define FU_FP_LATENCY      9

/* IDENTIFYING INSTRUCTIONS */

//unconditional branch, jump or call
#define IS_UNCOND_CTRL(op) (MD_OP_FLAGS(op) & F_CALL || \
                         MD_OP_FLAGS(op) & F_UNCOND)

//conditional branch instruction
#define IS_COND_CTRL(op) (MD_OP_FLAGS(op) & F_COND)

//floating-point computation
#define IS_FCOMP(op) (MD_OP_FLAGS(op) & F_FCOMP)

//integer computation
#define IS_ICOMP(op) (MD_OP_FLAGS(op) & F_ICOMP)

//load instruction
#define IS_LOAD(op)  (MD_OP_FLAGS(op) & F_LOAD)

//store instruction
#define IS_STORE(op) (MD_OP_FLAGS(op) & F_STORE)

//trap instruction
#define IS_TRAP(op) (MD_OP_FLAGS(op) & F_TRAP)

#define USES_INT_FU(op) (IS_ICOMP(op) || IS_LOAD(op) || IS_STORE(op))
#define USES_FP_FU(op) (IS_FCOMP(op))

#define WRITES_CDB(op) (IS_ICOMP(op) || IS_LOAD(op) || IS_FCOMP(op))

/* FOR DEBUGGING */

//prints info about an instruction
#define PRINT_INST(out,instr,str,cycle)	\
  myfprintf(out, "%d: %s", cycle, str);		\
  md_print_insn(instr->inst, instr->pc, out); \
  myfprintf(stdout, "(%d)\n",instr->index);

#define PRINT_REG(out,reg,str,instr) \
  myfprintf(out, "reg#%d %s ", reg, str);	\
  md_print_insn(instr->inst, instr->pc, out); \
  myfprintf(stdout, "(%d)\n",instr->index);

/* VARIABLES */

//instruction queue for tomasulo
static instruction_t* instr_queue[INSTR_QUEUE_SIZE];
//number of instructions in the instruction queue
static int instr_queue_size = 0;

/* ECE552 Assignment 3 - BEGIN CODE */
// For keeping track of where the head and tail of the queue is.
static int instr_queue_start = 0;
/* ECE552 Assignment 3 - END CODE */

//reservation stations (each reservation station entry contains a pointer to an instruction)
static instruction_t* reservINT[RESERV_INT_SIZE];
static instruction_t* reservFP[RESERV_FP_SIZE];

//functional units
static instruction_t* fuINT[FU_INT_SIZE];
static instruction_t* fuFP[FU_FP_SIZE];

//common data bus
static instruction_t* commonDataBus = NULL;

//The map table keeps track of which instruction produces the value for each register
static instruction_t* map_table[MD_TOTAL_REGS];

//the index of the last instruction fetched
/* ECE552 Assignment 3 - BEGIN CODE */
// Fetch index is zero-indexed.
static int fetch_index = -1;
/* ECE552 Assignment 3 - END CODE */

/* FUNCTIONAL UNITS */


/* RESERVATION STATIONS */


/*
 * Description:
 * 	Checks if simulation is done by finishing the very last instruction
 *      Remember that simulation is done only if the entire pipeline is empty
 * Inputs:
 * 	sim_insn: the total number of instructions simulated
 * Returns:
 * 	True: if simulation is finished
 */
static bool is_simulation_done(counter_t sim_insn) {

  /* ECE552: YOUR CODE GOES HERE */

  return true; //ECE552: you can change this as needed; we've added this so the code provided to you compiles
}

/*
 * Description:
 * 	Retires the instruction from writing to the Common Data Bus
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void CDB_To_retire(int current_cycle) {

  /* ECE552: YOUR CODE GOES HERE */

}


/*
 * Description:
 * 	Moves an instruction from the execution stage to common data bus (if possible)
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void execute_To_CDB(int current_cycle) {

  /* ECE552: YOUR CODE GOES HERE */

}

/*
 * Description:
 * 	Moves instruction(s) from the issue to the execute stage (if possible). We prioritize old instructions
 *      (in program order) over new ones, if they both contend for the same functional unit.
 *      All RAW dependences need to have been resolved with stalls before an instruction enters execute.
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void issue_To_execute(int current_cycle) {

  /* ECE552: YOUR CODE GOES HERE */
  int i, j;
  int freeFuINT = 0;
  int freeFuINTi[FU_INT_SIZE];
  int freeFuFP = 0;
  int freeFuFPi[FU_FP_SIZE];

  int ready;
  instruction_t *instr = NULL;
  instruction_t *old_instr = NULL;

  for (i = 0; i < FU_INT_SIZE; i++) {
    if (fuINT[i] == NULL) {
      freeFuINTi[i] = i;
      freeFuINT++;
    }
  }
  for (i = 0; i < FU_FP_SIZE; i++) {
    if (fuFP[i] == NULL) {
      freeFuFPi[i] = i;
      freeFuFP++;
    }
  }

  for (i = 0; i < freeFuINT; i++) {
    // Get the oldest instruction from reservINT
    old_instr = NULL;
    for (j = 0; j < RESERV_INT_SIZE; j++) {
      instr = reservINT[j];
      if (instr == NULL) continue;
      if (instr->tom_issue_cycle != 0) continue; // Issued.

      // Check if instruction is ready to execute.

      if (old_instr == NULL) {
        old_instr = instr;
      } else if (old_instr->index > instr->index){
        // Replace with older instruction
        old_instr = instr;
      }
    }
    if (old_instr == NULL) {
      // There's no instruction in the RS.
      break;
    }

    // Execute the oldest instruction.
    old_instr->tom_execute_cycle = current_cycle;

  }



  // Check all instructions in the reservation stations
  // Prioritize old instructions first.
  for (i = 0; i < RESERV_INT_SIZE; i++) {
    instr = reservINT[i];
    if (instr == NULL) continue;
    if (instr->tom_issue_cycle != 0) continue; // Already issued;

    // Check if the instruction has all the values it needs to proceed.
    // If all Q's are NULL, it means the instruction is good to go.
    ready = 1;
    for (j = 0; j < 3; j++) {
      ready &= (instr->Q[j] == NULL);
    }
    if (!ready) continue;

    // Check if a int FU is free.
    ready = 0;
    for (j = 0; j < FU_INT_SIZE; j++) {
      if (fuINT[j] == NULL) {
        fuINT[j] = instr;
        ready = 1;
        break;
      }
    }
    if (!ready) continue;

    // Issue the instruction
    //instr->tom_issue_cycle = current_cycle;
  }

  for (i = 0; i < RESERV_FP_SIZE; i++) {
    instr = reservFP[i];
    if (instr == NULL) continue;
    if (instr->tom_issue_cycle != 0) continue; // Already issued;

    // Check if the instruction has all the values it needs to proceed.
    // If all Q's are NULL, it means the instruction is good to go.
    ready = 1;
    for (j = 0; j < 3; j++) {
      ready &= (instr->Q[j] == NULL);
    }
    if (!ready) continue;

    // Check if a FP FU is free.
    ready = 0;
    for (j = 0; j < FU_FP_SIZE; j++) {
      if (fuFP[j] == NULL) {
        fuFP[j] = instr;
        ready = 1;
        break;
      }
    }
    if (!ready) continue;

    // Issue the instruction
    //instr->tom_issue_cycle = current_cycle;
  }

  // Check the issued cycle and execute older instructions first.
}

/*
 * Description:
 * 	Moves instruction(s) from the dispatch stage to the issue stage
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void dispatch_To_issue(int current_cycle) {

  /* ECE552: YOUR CODE GOES HERE */
  if (instr_queue_size <= 0) return;

  int i, j, reg_num;
  int issue = 0;
  instruction_t *instr = NULL;

  for (i = 0; i < INSTR_QUEUE_SIZE; i++) {
    instr = instr_queue[(instr_queue_start+i)%INSTR_QUEUE_SIZE];

    if (IS_COND_CTRL(instr->op) || IS_UNCOND_CTRL(instr->op)) {
      // Jump and branch can dispatch right away.
      instr->tom_issue_cycle = current_cycle;
      // Simply remove from instr queue.
      instr_queue[instr_queue_start] = NULL;
      instr_queue_start++;
      instr_queue_size--;
      continue;

    } else if (USES_INT_FU(instr->op)) {
      // Find available reservation station.
      for (j = 0; reservINT[j] != NULL; j++) {}
      if (j < RESERV_INT_SIZE) {
        reservINT[j] = instr;
        issue = 1;
      }

    } else if (USES_FP_FU(instr->op)) {
      // Find available reservation station.
      for (j = 0; reservFP[j] != NULL; j++) {}
      if (j < RESERV_FP_SIZE) {
        reservFP[j] = instr;
        issue = 1;
      }
    }

    if (issue) {
      instr->tom_issue_cycle = current_cycle;

      // Collect input values/tags first
      for (j = 0; j < 3; j++) {
        reg_num = instr->r_in[j];
        if (reg_num != 0 && map_table[reg_num] != NULL) {
          // Map table indicates that an input reg is not ready.
          instr->Q[j] = map_table[reg_num];
        }
      }

      // Update the map table with output reg
      for (j = 0; j < 2; j++) {
        reg_num = instr->r_out[j];
        if (reg_num != 0) {
          map_table[reg_num] = instr;
        }
      }

      // Remove instr from queue.
      instr_queue[instr_queue_start] = NULL;
      instr_queue_start++;
      instr_queue_size--;

    } else {
      // Cannot go from dispatch to issue out of order.
      return;
    }
  }
}

/*
 * Description:
 * 	Grabs an instruction from the instruction trace (if possible)
 * Inputs:
 *      trace: instruction trace with all the instructions executed
 * Returns:
 * 	None
 */
void fetch(instruction_trace_t* trace) {

  /* ECE552: YOUR CODE GOES HERE */
  instruction_t *new_instr = NULL;

  if (instr_queue_size < INSTR_QUEUE_SIZE) {

    // Fetch ONE instruction
    // fetch_index should be zero indexed.
    fetch_index++;
    new_instr = get_instr(trace, fetch_index);

    // Skip TRAP instructions
    while (new_instr != NULL && IS_TRAP(new_instr->op)) {
      fetch_index++;
      new_instr = get_instr(trace, fetch_index);
    }

    if (new_instr != NULL) {
      // Put instruction in end of queue
      int queue_end = (instr_queue_start + instr_queue_size) % INSTR_QUEUE_SIZE;
      instr_queue[queue_end] = new_instr;
      instr_queue_size++;
    }
  }
}




/*
 * Description:
 * 	Calls fetch and dispatches an instruction at the same cycle (if possible)
 * Inputs:
 *      trace: instruction trace with all the instructions executed
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void fetch_To_dispatch(instruction_trace_t* trace, int current_cycle) {

  fetch(trace);

  /* ECE552: YOUR CODE GOES HERE */
  if (instr_queue_size == 0) return;

  // Since we only dispatch one instruction at a time, we only need to look
  // at the last thing in the queue.
  int queue_end = (instr_queue_start + instr_queue_size - 1) % INSTR_QUEUE_SIZE;
  instruction_t *instr = instr_queue[queue_end];
  if (instr != NULL && instr->tom_dispatch_cycle != 0) {
    instr->tom_dispatch_cycle = current_cycle;
  }
}

/*
 * Description:
 * 	Performs a cycle-by-cycle simulation of the 4-stage pipeline
 * Inputs:
 *      trace: instruction trace with all the instructions executed
 * Returns:
 * 	The total number of cycles it takes to execute the instructions.
 * Extra Notes:
 * 	sim_num_insn: the number of instructions in the trace
 */
counter_t runTomasulo(instruction_trace_t* trace)
{
  //initialize instruction queue
  int i;
  for (i = 0; i < INSTR_QUEUE_SIZE; i++) {
    instr_queue[i] = NULL;
  }

  //initialize reservation stations
  for (i = 0; i < RESERV_INT_SIZE; i++) {
      reservINT[i] = NULL;
  }

  for(i = 0; i < RESERV_FP_SIZE; i++) {
      reservFP[i] = NULL;
  }

  //initialize functional units
  for (i = 0; i < FU_INT_SIZE; i++) {
    fuINT[i] = NULL;
  }

  for (i = 0; i < FU_FP_SIZE; i++) {
    fuFP[i] = NULL;
  }

  //initialize map_table to no producers
  int reg;
  for (reg = 0; reg < MD_TOTAL_REGS; reg++) {
    map_table[reg] = NULL;
  }

  int cycle = 1;
  while (true) {

     /* ECE552: YOUR CODE GOES HERE */

    // Write back
    // Execute
    // Dispatch
    // Fetch

     cycle++;

     if (is_simulation_done(sim_num_insn))
        break;
  }

  return cycle;
}
