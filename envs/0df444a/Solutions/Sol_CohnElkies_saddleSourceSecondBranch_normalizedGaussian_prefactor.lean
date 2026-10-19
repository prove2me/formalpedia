-- Prove2me | solution 1 for CohnElkies.saddleSourceSecondBranch_normalizedGaussian_prefactor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/3fd350ea-30a0-46f9-8cee-04a9843dfddb

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
    {ε ℓ δ : ℝ}
    (hℓ : 0 < ℓ)
    (hV : 0 < saddleSourceGaussianVariance ε ℓ (1 + δ)) :
    Real.sqrt
        (ℓ * saddleSourceGaussianVariance ε ℓ (1 + δ)) *
      Real.sqrt
        (Real.pi /
          (saddleSourceSecondBranchGaussianRate ε ℓ δ / 4)) =
      Real.sqrt (400 * Real.exp 1 * Real.pi) := by
  let V : ℝ := saddleSourceGaussianVariance ε ℓ (1 + δ)
  have hLV : 0 < ℓ * V := mul_pos hℓ hV
  have hVne : V ≠ 0 := by
    exact hV.ne'
  rw [← Real.sqrt_mul hLV.le]
  congr 1
  unfold saddleSourceSecondBranchGaussianRate
  change
    (ℓ * V) *
        (Real.pi / (((ℓ / (100 * Real.exp 1)) * V) / 4)) =
      400 * Real.exp 1 * Real.pi
  field_simp [hℓ.ne', hVne, (Real.exp_pos 1).ne']; ring
end CohnElkies
