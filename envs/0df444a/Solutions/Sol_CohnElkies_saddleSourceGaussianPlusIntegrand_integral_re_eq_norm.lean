-- Prove2me | solution 1 for CohnElkies.saddleSourceGaussianPlusIntegrand_integral_re_eq_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.271862+00:00
-- url     : https://prove2.me/submissions/c5f0dc15-8705-4aac-991c-4104253e125d

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_plusPolynomial_imaginary_re_pos
import Theorems.Thm_CohnElkies_saddleSourceGaussianKernel_integral
import Theorems.Thm_CohnElkies_saddleSourceGaussianPlusIntegrand_integral

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
    (hε : 0 < ε) (hu : -1 < u) :
    (∫ T : ℝ, saddleSourceGaussianPlusIntegrand ε ℓ u T).re =
      ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ *
        (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T) := by
  have hvalue : 0 < beta ε + (1 - u) ^ 2 * (1 + u) := by
    have h := plusPolynomial_imaginary_re_pos hε hu
    rw [plusPolynomial_imaginary, Complex.ofReal_re] at h
    exact h
  rw [saddleSourceGaussianPlusIntegrand_integral,
    saddleSourceGaussianKernel_integral,
    plusPolynomial_imaginary]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hvalue]
  ring
end CohnElkies
