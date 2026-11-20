-- Prove2me | solution 1 for DeletionCode.AlignmentTrace.Trace.matchedAnchor_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:04.787154+00:00
-- url     : https://prove2.me/submissions/a827c960-8d5f-416a-9d5c-fe34ffa5102a

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedCount_append

set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment
open DeletionCode.AlignmentTrace.Trace
namespace DeletionCode.AlignmentTrace.Trace
theorem _root_.solution (trace : Trace) (j : ℕ) :
    matchedAnchor trace j ≤ trace.matchedCount := by
  have h := matchedCount_append (trace.take j) (trace.drop j)
  rw [List.take_append_drop] at h
  unfold matchedAnchor
  omega
end DeletionCode.AlignmentTrace.Trace
