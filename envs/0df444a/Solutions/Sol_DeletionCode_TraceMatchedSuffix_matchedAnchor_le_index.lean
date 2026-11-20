-- Prove2me | solution 1 for DeletionCode.TraceMatchedSuffix.matchedAnchor_le_index
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:45:51.269615+00:00
-- url     : https://prove2.me/submissions/be9fc4b8-4b38-4c22-a498-b39405a5fca8

import Definitions.Def_DeletionCode_TraceSeparation
import Definitions.Def_DeletionCode_TraceMatchedSuffix
import Theorems.Thm_DeletionCode_TraceMatchedSuffix_matchedCount_le_length
import Theorems.Thm_DeletionCode_EditAlignment_Script_trans


set_option autoImplicit true
open DeletionCode DeletionCode.TraceMatchedSuffix
open AlignmentTrace FiniteConflictGraph TraceSeparation
namespace DeletionCode.TraceMatchedSuffix
theorem _root_.solution (trace : Trace) (i : ℕ) : trace.matchedAnchor i ≤ i := by
  have h := matchedCount_le_length (trace.take i)
  have hlen := List.length_take_le i trace
  exact h.trans hlen
end DeletionCode.TraceMatchedSuffix
