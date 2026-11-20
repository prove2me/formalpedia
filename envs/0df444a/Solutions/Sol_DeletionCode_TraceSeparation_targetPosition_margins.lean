-- Prove2me | solution 1 for DeletionCode.TraceSeparation.targetPosition_margins
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:43:57.937114+00:00
-- url     : https://prove2.me/submissions/d1a6c4b1-be52-426d-b792-0106a76e685b

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation
import Theorems.Thm_DeletionCode_TraceSeparation_counter_take_le
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_insertions_append
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_targetPosition_eq
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_target_length


set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph
namespace DeletionCode.TraceSeparation
theorem _root_.solution {trace : Trace} {B : ℕ}
    (hsep : Separated B trace) (i : Fin trace.length) (hi : EditIndex trace i) :
    B ≤ trace.targetPosition i.val ∧
      trace.targetPosition i.val + B ≤ trace.target.length := by
  have hm := hsep.1 i hi
  have hc := counter_take_le Trace.insertions Trace.insertions_append trace i.val
  have hp := trace.targetPosition_eq i.val
  have hn := trace.target_length
  constructor <;> omega
end DeletionCode.TraceSeparation
