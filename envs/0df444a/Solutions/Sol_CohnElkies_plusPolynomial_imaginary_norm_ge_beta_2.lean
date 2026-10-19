-- Prove2me | solution 2 for CohnElkies.plusPolynomial_imaginary_norm_ge_beta
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:17:20.0054+00:00
-- url     : https://prove2.me/submissions/28792adc-a639-4d19-8d81-16a8752b1799

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
    {ε u : ℝ} (hε : 0 < ε) (hu : -1 ≤ u) :
    beta ε ≤ ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ := by
  have key : plusPolynomial ε (Complex.I * (u : ℂ)) = (((1 - u) ^ 2 * (1 + u) + beta ε : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [plusPolynomial, pow_two, pow_succ] <;> ring
  rw [key, Complex.norm_real, Real.norm_eq_abs]
  refine le_trans ?_ (le_abs_self _)
  have : 0 ≤ (1 - u) ^ 2 * (1 + u) := mul_nonneg (sq_nonneg _) (by linarith)
  linarith

