-- Prove2me | solution 2 for CohnElkies.saddleNegativeContourOrdinate_add_rate_le_three
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:01:52.69765+00:00
-- url     : https://prove2.me/submissions/5d44f03d-122b-40ee-8e97-f2f540066376

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
    saddleNegativeContourOrdinate ℓ N +
        saddleNegativeGammaRate ℓ N ≤ 3 := by
  unfold saddleNegativeContourOrdinate saddleNegativeGammaRate
  push_cast at hN
  have : (2 * (N : ℝ) + 1) / ℓ + (2 * (N : ℝ) + 3) / ℓ ≤ 2 := by
    rw [← add_div, div_le_iff₀ hℓ]; linarith
  linarith

