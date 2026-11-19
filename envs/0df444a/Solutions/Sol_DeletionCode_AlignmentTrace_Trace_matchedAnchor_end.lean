-- Prove2me | solution 1 for DeletionCode.AlignmentTrace.Trace.matchedAnchor_end
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:20:26.98365+00:00
-- url     : https://prove2.me/submissions/2a220f54-34b2-48ae-a1cf-4ea5c8f2c767

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_zero
attribute [local simp] DeletionCode.AlignmentTrace.Trace.matchedAnchor_zero

set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment
open DeletionCode.AlignmentTrace.Trace
namespace DeletionCode.AlignmentTrace.Trace
theorem _root_.solution (trace : Trace) :
    matchedAnchor trace trace.length = trace.matchedCount := by
  simp [matchedAnchor]
end DeletionCode.AlignmentTrace.Trace
