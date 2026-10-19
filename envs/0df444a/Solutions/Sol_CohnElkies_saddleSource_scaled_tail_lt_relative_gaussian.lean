-- Prove2me | solution 1 for CohnElkies.saddleSource_scaled_tail_lt_relative_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/1fafc5da-8c9b-4a3c-b17d-40e791c7bbc3

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSourceGaussianKernel_scaled_integral

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε ℓ u C A κ X W : ℝ}
    (hℓ : 0 < ℓ)
    (hV : 0 < saddleSourceGaussianVariance ε ℓ u)
    (hC : 0 < C) (hA : 0 < A)
    (hbound : X ≤ C * A * W)
    (hnormalized :
      Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u) *
        W < κ) :
    X < (C * κ / Real.sqrt (2 * Real.pi)) * A *
      (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T) := by
  have hs : 0 <
      Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u) := by
    positivity
  have hg : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hmass := saddleSourceGaussianKernel_scaled_integral hℓ hV
  have hgaussian :
      (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T) =
        Real.sqrt (2 * Real.pi) /
          Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u) := by
    apply (eq_div_iff hs.ne').mpr
    nlinarith
  have hW :
      W < κ /
        Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u) := by
    apply (lt_div_iff₀ hs).mpr
    nlinarith
  calc
    X ≤ C * A * W := hbound
    _ < C * A *
        (κ / Real.sqrt
          (ℓ * saddleSourceGaussianVariance ε ℓ u)) := by
      exact mul_lt_mul_of_pos_left hW (mul_pos hC hA)
    _ = (C * κ / Real.sqrt (2 * Real.pi)) * A *
        (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T) := by
      rw [hgaussian]
      field_simp [hs.ne', hg.ne']
end CohnElkies
