-- Prove2me | solution 2 for CohnElkies.saddleNegativeContourOrdinate_le_two
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:16:15.838098+00:00
-- url     : https://prove2.me/submissions/9cacf33b-e933-42bf-87ad-872db6f78c1e

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators


theorem solution
    {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ)
    (hN : 2 * (((N + 1 : ℕ) : ℝ)) ≤ ℓ) :
    saddleNegativeContourOrdinate ℓ N ≤ 2 := by
  unfold saddleNegativeContourOrdinate
  push_cast at hN
  have : (2 * (N : ℝ) + 1) / ℓ ≤ 1 := by rw [div_le_one hℓ]; linarith
  linarith

