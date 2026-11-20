-- Prove2me | solution 1 for DeletionCode.TraceSeparation.targetPosition_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:51:05.630914+00:00
-- url     : https://prove2.me/submissions/fbbe0f9c-f1f4-47d9-ba3d-903cc7d41e61

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation
import Theorems.Thm_DeletionCode_TraceSeparation_insertions_take_mono
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_targetPosition_eq


set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph
namespace DeletionCode.TraceSeparation
theorem _root_.solution (trace : Trace) {i j B : ℕ} (hij : i ≤ j)
    (hgap : trace.matchedAnchor i + B ≤ trace.matchedAnchor j) :
    trace.targetPosition i + B ≤ trace.targetPosition j := by
  have hc := insertions_take_mono trace hij
  have hi := trace.targetPosition_eq i
  have hj := trace.targetPosition_eq j
  omega
end DeletionCode.TraceSeparation
