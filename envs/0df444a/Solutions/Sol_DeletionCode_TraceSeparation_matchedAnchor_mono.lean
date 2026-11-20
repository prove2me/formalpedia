-- Prove2me | solution 1 for DeletionCode.TraceSeparation.matchedAnchor_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:46:44.29193+00:00
-- url     : https://prove2.me/submissions/897fb61a-1041-4aff-99ca-195158f82442

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation
import Theorems.Thm_DeletionCode_TraceSeparation_counter_take_mono
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedCount_append


set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph
namespace DeletionCode.TraceSeparation
theorem _root_.solution (trace : Trace) {i j : ℕ} (hij : i ≤ j) :
    trace.matchedAnchor i ≤ trace.matchedAnchor j :=
  counter_take_mono Trace.matchedCount Trace.matchedCount_append trace hij
end DeletionCode.TraceSeparation
