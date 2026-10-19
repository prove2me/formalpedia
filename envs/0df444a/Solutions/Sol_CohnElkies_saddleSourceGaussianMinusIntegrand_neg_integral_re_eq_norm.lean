-- Prove2me | solution 1 for CohnElkies.saddleSourceGaussianMinusIntegrand_neg_integral_re_eq_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.271862+00:00
-- url     : https://prove2.me/submissions/a389fd0e-5c2c-4f5f-a35c-81456f328ab8

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_minusPolynomial_imaginary_re_neg
import Theorems.Thm_CohnElkies_saddleSourceGaussianKernel_integral
import Theorems.Thm_CohnElkies_saddleSourceGaussianMinusIntegrand_integral

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hu : 1 + ε / 4 ≤ u) :
    -(∫ T : ℝ, saddleSourceGaussianMinusIntegrand ε ℓ u T).re =
      ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ *
        (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T) := by
  have hvalue : beta ε + (1 - u) * (1 + u) ^ 2 < 0 := by
    have h := minusPolynomial_imaginary_re_neg hε hu
    rw [minusPolynomial_imaginary, Complex.ofReal_re] at h
    exact h
  rw [saddleSourceGaussianMinusIntegrand_integral,
    saddleSourceGaussianKernel_integral,
    minusPolynomial_imaginary]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.norm_real, Real.norm_eq_abs,
    abs_of_neg hvalue]
  ring
end CohnElkies
