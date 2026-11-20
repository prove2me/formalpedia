-- Prove2me | solution 1 for DeletionCode.TraceSeparation.insertions_take_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:46:45.257232+00:00
-- url     : https://prove2.me/submissions/3100f019-d70e-4eda-9eb6-07fdb0d09323

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation
import Theorems.Thm_DeletionCode_TraceSeparation_counter_take_mono
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_insertions_append


set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph
namespace DeletionCode.TraceSeparation
theorem _root_.solution (trace : Trace) {i j : ℕ} (hij : i ≤ j) :
    Trace.insertions (trace.take i) ≤ Trace.insertions (trace.take j) :=
  counter_take_mono Trace.insertions Trace.insertions_append trace hij
end DeletionCode.TraceSeparation
