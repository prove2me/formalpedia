-- Prove2me | solution 1 for DeletionCode.AlignmentTrace.Trace.deletions_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:32:20.868254+00:00
-- url     : https://prove2.me/submissions/946d295e-a0c2-4b68-87e9-46100438479c

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace

set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment
open DeletionCode.AlignmentTrace.Trace
namespace DeletionCode.AlignmentTrace.Trace
theorem _root_.solution (left right : Trace) :
    deletions (left ++ right) = deletions left + deletions right := by
  induction left with
  | nil => simp [deletions]
  | cons col rest ih =>
    cases col <;> simp only [List.cons_append, deletions, ih] <;> omega
end DeletionCode.AlignmentTrace.Trace
