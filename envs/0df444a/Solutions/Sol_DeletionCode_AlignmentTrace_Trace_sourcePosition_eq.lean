-- Prove2me | solution 1 for DeletionCode.AlignmentTrace.Trace.sourcePosition_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:32:24.343209+00:00
-- url     : https://prove2.me/submissions/b70b1224-5db7-4199-a3ca-70f8f6ea7092

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_source_length

set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment
open DeletionCode.AlignmentTrace.Trace
namespace DeletionCode.AlignmentTrace.Trace
theorem _root_.solution (trace : Trace) (j : ℕ) :
    sourcePosition trace j = matchedAnchor trace j + deletions (trace.take j) :=
  source_length (trace.take j)
end DeletionCode.AlignmentTrace.Trace
