-- Prove2me | solution 1 for CohnElkies.saddleSourceSecondBranch_normalizedGaussian_exponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/3e622679-324b-4d05-bf4f-bfb847fb8050

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
namespace CohnElkies
theorem _root_.solution
    {ε ℓ δ z : ℝ}
    (hℓ : 0 < ℓ)
    (hV : 0 < saddleSourceGaussianVariance ε ℓ (1 + δ)) :
    (saddleSourceSecondBranchGaussianRate ε ℓ δ / 4) *
        (z / Real.sqrt
          (ℓ * saddleSourceGaussianVariance ε ℓ (1 + δ))) ^ 2 =
      z ^ 2 / (400 * Real.exp 1) := by
  let V : ℝ := saddleSourceGaussianVariance ε ℓ (1 + δ)
  have hLV : 0 < ℓ * V := mul_pos hℓ hV
  have hVne : V ≠ 0 := by
    exact hV.ne'
  unfold saddleSourceSecondBranchGaussianRate
  change
    (((ℓ / (100 * Real.exp 1)) * V) / 4) *
        (z / Real.sqrt (ℓ * V)) ^ 2 =
      z ^ 2 / (400 * Real.exp 1)
  rw [div_pow, Real.sq_sqrt hLV.le]
  field_simp [hℓ.ne', hVne, (Real.exp_pos 1).ne']; ring
end CohnElkies
