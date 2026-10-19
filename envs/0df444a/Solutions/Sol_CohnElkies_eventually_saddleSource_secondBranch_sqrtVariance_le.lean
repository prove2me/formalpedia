-- Prove2me | solution 1 for CohnElkies.eventually_saddleSource_secondBranch_sqrtVariance_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/7173a8e5-641b-45e7-98e9-4c9ac8b93367

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSourceSecondBranchVarianceCoefficient_pos
import Theorems.Thm_CohnElkies_eventually_saddleSourceGaussianVariance_secondBranch_upper

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ ℓ : ℝ, 1 ≤ ℓ →
        ∀ δ : ℝ, ε / 2 ≤ δ →
          Real.sqrt
              (ℓ * saddleSourceGaussianVariance
                ε ℓ (1 + δ)) ≤
            Real.sqrt
                (saddleSourceSecondBranchVarianceCoefficient ε) *
              Real.sqrt ℓ *
                Real.exp
                  (((shellLocation ε + 1) / 2) * δ) := by
  filter_upwards
    [eventually_saddleSourceGaussianVariance_secondBranch_upper]
    with ε hupper
  intro ℓ hℓ δ hδ
  let C : ℝ := saddleSourceSecondBranchVarianceCoefficient ε
  have hC : 0 < C :=
    saddleSourceSecondBranchVarianceCoefficient_pos ε
  have hℓpositive : 0 < ℓ := by linarith
  have hsource := hupper ℓ hℓ δ hδ
  have hscaled := mul_le_mul_of_nonneg_left
    hsource hℓpositive.le
  calc
    Real.sqrt
        (ℓ * saddleSourceGaussianVariance ε ℓ (1 + δ)) ≤
      Real.sqrt
        (ℓ * (C * Real.exp
          ((shellLocation ε + 1) * δ))) := by
        apply Real.sqrt_le_sqrt
        simpa [C] using! hscaled
    _ = Real.sqrt C * Real.sqrt ℓ *
        Real.exp
          (((shellLocation ε + 1) / 2) * δ) := by
      rw [Real.sqrt_mul hℓpositive.le,
        Real.sqrt_mul hC.le, ← Real.exp_half]
      have hargument :
          ((shellLocation ε + 1) * δ) / 2 =
            ((shellLocation ε + 1) / 2) * δ := by
        ring
      rw [hargument]
      ring
end CohnElkies
