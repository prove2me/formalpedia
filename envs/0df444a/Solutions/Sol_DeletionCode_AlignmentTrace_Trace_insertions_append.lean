-- Prove2me | solution 1 for DeletionCode.AlignmentTrace.Trace.insertions_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:32:22.080329+00:00
-- url     : https://prove2.me/submissions/5d9b5c22-2142-4f08-b60e-86a1121d2aac

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace

set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment
open DeletionCode.AlignmentTrace.Trace
namespace DeletionCode.AlignmentTrace.Trace
theorem _root_.solution (left right : Trace) :
    insertions (left ++ right) = insertions left + insertions right := by
  induction left with
  | nil => simp [insertions]
  | cons col rest ih =>
    cases col <;> simp only [List.cons_append, insertions, ih] <;> omega
end DeletionCode.AlignmentTrace.Trace
