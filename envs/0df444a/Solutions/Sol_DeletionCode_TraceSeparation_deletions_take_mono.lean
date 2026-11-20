-- Prove2me | solution 1 for DeletionCode.TraceSeparation.deletions_take_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:46:44.726949+00:00
-- url     : https://prove2.me/submissions/e1b86388-c0ba-4b5d-9968-1f095ca758ec

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation
import Theorems.Thm_DeletionCode_TraceSeparation_counter_take_mono
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_deletions_append


set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph
namespace DeletionCode.TraceSeparation
theorem _root_.solution (trace : Trace) {i j : ℕ} (hij : i ≤ j) :
    Trace.deletions (trace.take i) ≤ Trace.deletions (trace.take j) :=
  counter_take_mono Trace.deletions Trace.deletions_append trace hij
end DeletionCode.TraceSeparation
