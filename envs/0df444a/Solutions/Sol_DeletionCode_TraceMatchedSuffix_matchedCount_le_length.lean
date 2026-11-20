-- Prove2me | solution 1 for DeletionCode.TraceMatchedSuffix.matchedCount_le_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:41:23.061184+00:00
-- url     : https://prove2.me/submissions/52093d48-55f6-4a87-a432-695d480c3dfc

import Definitions.Def_DeletionCode_TraceSeparation
import Definitions.Def_DeletionCode_TraceMatchedSuffix
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_length_eq_counts


set_option autoImplicit true
open DeletionCode DeletionCode.TraceMatchedSuffix
open AlignmentTrace FiniteConflictGraph TraceSeparation
namespace DeletionCode.TraceMatchedSuffix
theorem _root_.solution (trace : Trace) : trace.matchedCount ≤ trace.length := by
  have h := trace.length_eq_counts
  omega
end DeletionCode.TraceMatchedSuffix
