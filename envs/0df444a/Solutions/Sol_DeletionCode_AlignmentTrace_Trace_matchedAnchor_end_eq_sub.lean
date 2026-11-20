-- Prove2me | solution 1 for DeletionCode.AlignmentTrace.Trace.matchedAnchor_end_eq_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:56.68243+00:00
-- url     : https://prove2.me/submissions/d39d9a69-18de-468e-a0e5-557bb63dfc07

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_AlignmentTrace
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_source_length
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_end
attribute [local simp] DeletionCode.AlignmentTrace.Trace.matchedAnchor_end

set_option autoImplicit true
open DeletionCode DeletionCode.AlignmentTrace
open EditAlignment
open DeletionCode.AlignmentTrace.Trace
namespace DeletionCode.AlignmentTrace.Trace
theorem _root_.solution (trace : Trace) (n d : ℕ)
    (hsource : trace.source.length = n) (hdel : trace.deletions = d) :
    matchedAnchor trace trace.length = n - d := by
  rw [matchedAnchor_end]
  have h := source_length trace
  omega
end DeletionCode.AlignmentTrace.Trace
