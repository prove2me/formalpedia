-- Prove2me | solution 1 for DeletionCode.TraceSeparation.sourcePosition_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:51:04.797027+00:00
-- url     : https://prove2.me/submissions/9ada03dd-a2bf-4f9a-9ffb-403e6fb20293

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation
import Theorems.Thm_DeletionCode_TraceSeparation_deletions_take_mono
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_sourcePosition_eq


set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph
namespace DeletionCode.TraceSeparation
theorem _root_.solution (trace : Trace) {i j B : ℕ} (hij : i ≤ j)
    (hgap : trace.matchedAnchor i + B ≤ trace.matchedAnchor j) :
    trace.sourcePosition i + B ≤ trace.sourcePosition j := by
  have hc := deletions_take_mono trace hij
  have hi := trace.sourcePosition_eq i
  have hj := trace.sourcePosition_eq j
  omega
end DeletionCode.TraceSeparation
