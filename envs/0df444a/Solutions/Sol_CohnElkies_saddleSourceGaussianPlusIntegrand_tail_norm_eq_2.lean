-- Prove2me | solution 2 for CohnElkies.saddleSourceGaussianPlusIntegrand_tail_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:34:16.518988+00:00
-- url     : https://prove2.me/submissions/2423a108-adf7-410f-9b88-2577aa7a809f

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
    (ε ℓ u R : ℝ) :
    (∫ T : ℝ in saddleGaussianTailSet R,
      ‖saddleSourceGaussianPlusIntegrand ε ℓ u T‖) =
      ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ *
        (∫ T : ℝ in saddleGaussianTailSet R,
          saddleSourceGaussianKernel ε ℓ u T) := by
  have h : ∀ T : ℝ, ‖saddleSourceGaussianPlusIntegrand ε ℓ u T‖ =
      ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ * saddleSourceGaussianKernel ε ℓ u T := by
    intro T
    unfold saddleSourceGaussianPlusIntegrand
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by unfold saddleSourceGaussianKernel; exact Real.exp_pos _)]
    ring
  simp_rw [h]
  rw [MeasureTheory.integral_const_mul]

