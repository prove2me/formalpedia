-- Prove2me | solution 2 for CohnElkies.saddleSourceGaussianKernel_scaled_integral
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:21:44.910763+00:00
-- url     : https://prove2.me/submissions/b7e476e6-4d28-4701-adbf-92b22ca49210

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
    {ε ℓ u : ℝ}
    (hℓ : 0 < ℓ)
    (hV : 0 < saddleSourceGaussianVariance ε ℓ u) :
    Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u) *
        (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T) =
      Real.sqrt (2 * Real.pi) := by
  unfold saddleSourceGaussianKernel
  rw [integral_gaussian]
  have hp : 0 < ℓ * saddleSourceGaussianVariance ε ℓ u := mul_pos hℓ hV
  rw [← Real.sqrt_mul hp.le]
  congr 1
  field_simp

