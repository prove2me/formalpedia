-- Prove2me | solution 2 for CohnElkies.saddleSource_scaled_tail_lt_relative_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:08:44.4216+00:00
-- url     : https://prove2.me/submissions/32e176ae-4e50-437a-bff0-b2718e9b5db0

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
  have hs : 0 < Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u) := Real.sqrt_pos.2 (by positivity)
  have h2 : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hI : (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T) =
      Real.sqrt (Real.pi / (ℓ * saddleSourceGaussianVariance ε ℓ u / 2)) := by
    unfold saddleSourceGaussianKernel
    exact integral_gaussian _
  have hq : Real.sqrt (Real.pi / (ℓ * saddleSourceGaussianVariance ε ℓ u / 2)) =
      Real.sqrt (2 * Real.pi) / Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u) := by
    rw [← Real.sqrt_div (by positivity)]
    congr 1
    field_simp
  rw [hI, hq]
  have hW : W < κ / Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u) := by
    rw [lt_div_iff₀ hs]; linarith
  have hCA : 0 < C * A := mul_pos hC hA
  calc X ≤ C * A * W := hbound
    _ < C * A * (κ / Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u)) :=
        mul_lt_mul_of_pos_left hW hCA
    _ = C * κ / Real.sqrt (2 * Real.pi) * A *
          (Real.sqrt (2 * Real.pi) / Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u)) := by
        field_simp

