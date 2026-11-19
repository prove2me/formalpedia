-- Prove2me | solution 1 for DeletionCode.AlignmentTrace.Trace.targetPosition_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:32:54.500955+00:00
-- url     : https://prove2.me/submissions/d4920462-500c-4d3a-bd84-f6ea37188dd5

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_target_length

set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment
open DeletionCode.AlignmentTrace.Trace
namespace DeletionCode.AlignmentTrace.Trace
theorem _root_.solution (trace : Trace) (j : ℕ) :
    targetPosition trace j = matchedAnchor trace j + insertions (trace.take j) :=
  target_length (trace.take j)
end DeletionCode.AlignmentTrace.Trace
