-- Prove2me | solution 2 for CohnElkies.eventually_saddleSmallResidueTruncation_dominates_window
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:21:58.792347+00:00
-- url     : https://prove2.me/submissions/56cf72df-8009-4228-bf41-f28761f2c755

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology


theorem solution
    {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ ℓ : ℝ in atTop,
      ∀ y : ℝ,
        0 ≤ y → y ≤ Real.log ℓ / 8 + C →
          2 * y ≤
            (saddleSmallResidueTruncation ℓ : ℝ) + 2 := by
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (8 * C)] with ℓ hℓ y hy0 hy1
  have := Nat.le_ceil (20 * Real.log ℓ)
  unfold saddleSmallResidueTruncation
  linarith

