-- Prove2me | solution 2 for CohnElkies.saddleSourceGaussianMinusIntegrand_tail_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:10:41.176279+00:00
-- url     : https://prove2.me/submissions/2e8c469f-b3cc-4c9f-8321-f98a4293378d

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
      ‖saddleSourceGaussianMinusIntegrand ε ℓ u T‖) =
      ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ *
        (∫ T : ℝ in saddleGaussianTailSet R,
          saddleSourceGaussianKernel ε ℓ u T) := by
  unfold saddleSourceGaussianMinusIntegrand
  have h : ∀ T, ‖(saddleSourceGaussianKernel ε ℓ u T : ℂ) * minusPolynomial ε (Complex.I * (u : ℂ))‖ =
      saddleSourceGaussianKernel ε ℓ u T * ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by
    intro T
    rw [norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (by unfold saddleSourceGaussianKernel; positivity)]
  simp_rw [h]
  rw [MeasureTheory.integral_mul_const]
  ring

