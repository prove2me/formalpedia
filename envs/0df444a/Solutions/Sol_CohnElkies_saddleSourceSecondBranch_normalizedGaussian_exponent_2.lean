-- Prove2me | solution 2 for CohnElkies.saddleSourceSecondBranch_normalizedGaussian_exponent
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:21:59.026743+00:00
-- url     : https://prove2.me/submissions/7932b79b-2cd8-49d4-88e8-97c6be83942d

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology


theorem solution
    {ε ℓ δ z : ℝ}
    (hℓ : 0 < ℓ)
    (hV : 0 < saddleSourceGaussianVariance ε ℓ (1 + δ)) :
    (saddleSourceSecondBranchGaussianRate ε ℓ δ / 4) *
        (z / Real.sqrt
          (ℓ * saddleSourceGaussianVariance ε ℓ (1 + δ))) ^ 2 =
      z ^ 2 / (400 * Real.exp 1) := by
  have hp : 0 < ℓ * saddleSourceGaussianVariance ε ℓ (1 + δ) := mul_pos hℓ hV
  unfold saddleSourceSecondBranchGaussianRate
  rw [div_pow, Real.sq_sqrt hp.le]
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  field_simp
  ring

