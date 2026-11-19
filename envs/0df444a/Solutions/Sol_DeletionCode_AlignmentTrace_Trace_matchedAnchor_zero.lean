-- Prove2me | solution 1 for DeletionCode.AlignmentTrace.Trace.matchedAnchor_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:20:01.272089+00:00
-- url     : https://prove2.me/submissions/69d400b9-9c9a-4d83-a083-dd51c1069204

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace

set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment
open DeletionCode.AlignmentTrace.Trace
namespace DeletionCode.AlignmentTrace.Trace
theorem _root_.solution (trace : Trace) : matchedAnchor trace 0 = 0 := rfl
end DeletionCode.AlignmentTrace.Trace
