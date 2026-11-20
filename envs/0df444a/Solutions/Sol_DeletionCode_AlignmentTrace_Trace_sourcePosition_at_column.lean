-- Prove2me | solution 1 for DeletionCode.AlignmentTrace.Trace.sourcePosition_at_column
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:55.603809+00:00
-- url     : https://prove2.me/submissions/5e4e9aab-4884-4f0a-8c57-1877cd5aed40

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace

set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment
open DeletionCode.AlignmentTrace.Trace
namespace DeletionCode.AlignmentTrace.Trace
theorem _root_.solution (pre suffix : Trace) (col : Column) :
    sourcePosition (pre ++ col :: suffix) pre.length = pre.source.length := by
  simp [sourcePosition]
end DeletionCode.AlignmentTrace.Trace
