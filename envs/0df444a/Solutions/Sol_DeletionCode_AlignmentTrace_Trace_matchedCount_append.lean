-- Prove2me | solution 1 for DeletionCode.AlignmentTrace.Trace.matchedCount_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:32:22.93321+00:00
-- url     : https://prove2.me/submissions/aa569a09-d993-4ed0-bb89-5b6d5c0ba8f6

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace

set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment
open DeletionCode.AlignmentTrace.Trace
namespace DeletionCode.AlignmentTrace.Trace
theorem _root_.solution (left right : Trace) :
    matchedCount (left ++ right) = matchedCount left + matchedCount right := by
  induction left with
  | nil => simp [matchedCount]
  | cons col rest ih =>
    cases col <;> simp only [List.cons_append, matchedCount, ih] <;> omega
end DeletionCode.AlignmentTrace.Trace
