-- Prove2me | solution 1 for DeletionCode.AlignmentTrace.Trace.matchedAnchor_at_column
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:55.088895+00:00
-- url     : https://prove2.me/submissions/9072eb0b-8970-4da1-9b28-48b10b8ddff8

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace

set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment
open DeletionCode.AlignmentTrace.Trace
namespace DeletionCode.AlignmentTrace.Trace
theorem _root_.solution (pre suffix : Trace) (col : Column) :
    matchedAnchor (pre ++ col :: suffix) pre.length = pre.matchedCount := by
  simp [matchedAnchor]
end DeletionCode.AlignmentTrace.Trace
