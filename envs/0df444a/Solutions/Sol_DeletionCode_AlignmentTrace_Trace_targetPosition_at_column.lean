-- Prove2me | solution 1 for DeletionCode.AlignmentTrace.Trace.targetPosition_at_column
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:56.20237+00:00
-- url     : https://prove2.me/submissions/05847a09-24a8-4532-83e8-b51c9cadf4f6

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace

set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment
open DeletionCode.AlignmentTrace.Trace
namespace DeletionCode.AlignmentTrace.Trace
theorem _root_.solution (pre suffix : Trace) (col : Column) :
    targetPosition (pre ++ col :: suffix) pre.length = pre.target.length := by
  simp [targetPosition]
end DeletionCode.AlignmentTrace.Trace
