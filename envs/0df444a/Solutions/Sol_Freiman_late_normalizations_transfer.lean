-- Prove2me | solution 1 for Freiman.late_normalizations_transfer
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:15:21.025514+00:00
-- url     : https://prove2.me/submissions/af09d432-dc8a-4fad-88b0-f655ee0587b5

import Theorems.Thm_Freiman_late_normalizations_from_width
import Theorems.Thm_Freiman_lowerHistory_width_threshold
import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 0

open Freiman

theorem solution : ∀ (p : LowerPair) (path : LatePath), latePathValid lateCatalog path → lateHolds (lateBounds lateCatalog path.required) (lateR p) (lateS p) (lateQ p) → ∀ n ∈ path.normalizations, lateNormalizationHolds p n := by
  exact late_normalizations_from_width lowerHistory_width_threshold
