-- Prove2me | solution 1 for DeletionCode.AlignmentTrace.Trace.length_eq_counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:00.660066+00:00
-- url     : https://prove2.me/submissions/94b9324f-a603-4769-8fc2-b400917fed1b

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace

set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment
open DeletionCode.AlignmentTrace.Trace
namespace DeletionCode.AlignmentTrace.Trace
theorem _root_.solution (trace : Trace) :
    trace.length = trace.matchedCount + trace.deletions + trace.insertions := by
  induction trace with
  | nil => rfl
  | cons col rest ih =>
    cases col <;>
      simp only [List.length_cons, matchedCount, deletions, insertions] <;> omega
end DeletionCode.AlignmentTrace.Trace
