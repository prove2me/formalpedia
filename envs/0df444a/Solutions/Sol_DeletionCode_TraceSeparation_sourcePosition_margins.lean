-- Prove2me | solution 1 for DeletionCode.TraceSeparation.sourcePosition_margins
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:43:54.691198+00:00
-- url     : https://prove2.me/submissions/707aa97c-d3c3-453f-88e4-214eddeb0d5b

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation
import Theorems.Thm_DeletionCode_TraceSeparation_counter_take_le
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_deletions_append
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_sourcePosition_eq
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_source_length


set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph
namespace DeletionCode.TraceSeparation
theorem _root_.solution {trace : Trace} {B : ℕ}
    (hsep : Separated B trace) (i : Fin trace.length) (hi : EditIndex trace i) :
    B ≤ trace.sourcePosition i.val ∧
      trace.sourcePosition i.val + B ≤ trace.source.length := by
  have hm := hsep.1 i hi
  have hc := counter_take_le Trace.deletions Trace.deletions_append trace i.val
  have hp := trace.sourcePosition_eq i.val
  have hn := trace.source_length
  constructor <;> omega
end DeletionCode.TraceSeparation
