-- Prove2me | solution 2 for CohnElkies.saddleSourceGaussianMinusIntegrand_neg_integral_re_eq_norm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:10:24.777325+00:00
-- url     : https://prove2.me/submissions/de7e1c03-51fa-4f2d-bf18-300af77731c8

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology


theorem solution
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hu : 1 + ε / 4 ≤ u) :
    -(∫ T : ℝ, saddleSourceGaussianMinusIntegrand ε ℓ u T).re =
      ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ *
        (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T) := by
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hm : minusPolynomial ε (Complex.I * (u:ℂ)) = (((1 - u^2) * (1 + u) + ε/4 : ℝ) : ℂ) := by
    unfold minusPolynomial beta
    push_cast
    linear_combination ((u:ℂ)^2 - u - (Complex.I^2 - 1) * (u:ℂ)^3) * hI
  have hneg : (1 - u^2) * (1 + u) + ε/4 < 0 := by nlinarith
  unfold saddleSourceGaussianMinusIntegrand
  rw [MeasureTheory.integral_mul_const, integral_complex_ofReal, hm, ← Complex.ofReal_mul, Complex.ofReal_re,
    Complex.norm_real, Real.norm_of_nonpos hneg.le]
  ring

