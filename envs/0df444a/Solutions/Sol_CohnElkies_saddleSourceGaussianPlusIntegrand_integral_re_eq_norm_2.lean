-- Prove2me | solution 2 for CohnElkies.saddleSourceGaussianPlusIntegrand_integral_re_eq_norm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:34:56.184904+00:00
-- url     : https://prove2.me/submissions/046b2789-5498-4d78-bb0b-0735d7dca591

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
    (hε : 0 < ε) (hu : -1 < u) :
    (∫ T : ℝ, saddleSourceGaussianPlusIntegrand ε ℓ u T).re =
      ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ *
        (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T) := by
  have key : plusPolynomial ε (Complex.I * (u : ℂ)) = (((1 - u) ^ 2 * (1 + u) + beta ε : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [plusPolynomial, pow_two, pow_succ] <;> ring
  have hnn : 0 ≤ (1 - u) ^ 2 * (1 + u) + beta ε := by
    have : 0 ≤ (1 - u) ^ 2 * (1 + u) := mul_nonneg (sq_nonneg _) (by linarith)
    have : 0 < beta ε := by unfold beta; linarith
    linarith
  unfold saddleSourceGaussianPlusIntegrand
  rw [integral_mul_const, integral_complex_ofReal, key, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

