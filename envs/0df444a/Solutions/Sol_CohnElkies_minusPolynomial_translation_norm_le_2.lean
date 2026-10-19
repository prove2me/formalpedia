-- Prove2me | solution 2 for CohnElkies.minusPolynomial_translation_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:20:07.874803+00:00
-- url     : https://prove2.me/submissions/e9a49b56-f556-42d6-944d-fdd8b2922643

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
    (ε u T : ℝ) :
    ‖minusPolynomial ε ((T : ℂ) + Complex.I * (u : ℂ)) -
        minusPolynomial ε (Complex.I * (u : ℂ))‖ ≤
      9 * (1 + |u|) ^ 2 * (|T| + |T| ^ 3) := by
  have hdiff : minusPolynomial ε ((T : ℂ) + Complex.I * (u : ℂ)) -
      minusPolynomial ε (Complex.I * (u : ℂ)) =
      ((T ^ 2 * (1 + 3 * u) : ℝ) : ℂ) + Complex.I * ((T * (3 * u ^ 2 + 2 * u - 1) - T ^ 3 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [minusPolynomial, pow_two, pow_three] <;> ring
  rw [hdiff]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs]
  have ht := abs_nonneg T
  have hs := abs_nonneg u
  have h1 : |T ^ 2 * (1 + 3 * u)| ≤ |T| ^ 2 * (1 + 3 * |u|) := by
    rw [abs_mul, abs_pow]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine (abs_add_le _ _).trans ?_
    rw [abs_one, abs_mul]; norm_num
  have h2 : |3 * u ^ 2 + 2 * u - 1| ≤ 3 * |u| ^ 2 + 2 * |u| + 1 := by
    refine (abs_sub _ _).trans ?_
    refine add_le_add ((abs_add_le _ _).trans (le_of_eq ?_)) (by norm_num)
    rw [abs_mul, abs_mul, abs_pow]; norm_num
  have h3 : |T * (3 * u ^ 2 + 2 * u - 1) - T ^ 3| ≤ |T| * (3 * |u| ^ 2 + 2 * |u| + 1) + |T| ^ 3 := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_pow]
    gcongr
  have ht2 : |T| ^ 2 ≤ |T| + |T| ^ 3 := by nlinarith [mul_nonneg ht (sq_nonneg (|T| - 1 / 2))]
  have h4 : |T| ^ 2 * (1 + 3 * |u|) ≤ (|T| + |T| ^ 3) * (1 + 3 * |u|) :=
    mul_le_mul_of_nonneg_right ht2 (by positivity)
  nlinarith [mul_nonneg hs ht, mul_nonneg (mul_nonneg hs hs) ht, mul_nonneg hs (pow_nonneg ht 3),
    mul_nonneg (mul_nonneg hs hs) (pow_nonneg ht 3), pow_nonneg ht 3]

