-- Prove2me | solution 2 for CohnElkies.upperImaginaryExp_centered_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:20:13.06354+00:00
-- url     : https://prove2.me/submissions/5be3b13a-0d63-491b-9e0b-b490bdfe1e75

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
    (x : ℝ) :
    ‖upperImaginaryExp x - 1 -
        Complex.I * (x : ℂ)‖ ≤
      x ^ 2 / 2 + |x| ^ 3 / 6 := by
  have hw : upperImaginaryExp x - 1 - Complex.I * (x : ℂ) =
      ((Real.cos x - 1 : ℝ) : ℂ) + ((Real.sin x - x : ℝ) : ℂ) * Complex.I := by
    unfold upperImaginaryExp
    rw [mul_comm, Complex.exp_mul_I]
    push_cast
    ring
  rw [hw]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have h1 : |Real.cos x - 1| ≤ x ^ 2 / 2 := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith [Real.cos_le_one x])]
    linarith [Real.one_sub_sq_div_two_le_cos (x := x)]
  have h2 : |Real.sin x - x| ≤ |x| ^ 3 / 6 := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx, abs_sub_comm, abs_of_nonneg (by linarith [Real.sin_le hx])]
      linarith [Real.sin_ge_sub_cube hx]
    · have a1 := Real.sin_le (neg_nonneg.2 hx)
      have a2 := Real.sin_ge_sub_cube (neg_nonneg.2 hx)
      rw [Real.sin_neg] at a1 a2
      rw [abs_of_nonpos hx, abs_of_nonneg (by linarith)]
      have : (-x) ^ 3 = -x ^ 3 := by ring
      linarith
  linarith

