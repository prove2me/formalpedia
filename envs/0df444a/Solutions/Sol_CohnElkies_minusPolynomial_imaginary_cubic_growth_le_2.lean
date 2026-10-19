-- Prove2me | solution 2 for CohnElkies.minusPolynomial_imaginary_cubic_growth_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:19:12.587681+00:00
-- url     : https://prove2.me/submissions/a71c3760-a6f4-4fb5-ba68-0265929ccf05

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
    {ε u : ℝ} (hε : 0 < ε)
    (hu : 1 + ε / 4 ≤ u) :
    (1 + |u|) ^ 3 ≤
      (9 / beta ε + 6) *
        ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by
  have hb : 0 < beta ε := beta_pos hε
  have hbeq : beta ε = ε / 4 := rfl
  have hu1 : beta ε ≤ u - 1 := by rw [hbeq]; linarith
  have hu0 : 1 ≤ u := by linarith
  rw [minusPolynomial_imaginary, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ u)]
  have hsq : 4 ≤ (1 + u) ^ 2 := by nlinarith
  have hneg : beta ε + (1 - u) * (1 + u) ^ 2 ≤ 0 := by nlinarith
  rw [abs_of_nonpos hneg]
  set X := -(beta ε + (1 - u) * (1 + u) ^ 2) with hXdef
  have hX1 : (u - 1) * (u * (u + 2)) ≤ X := by rw [hXdef]; nlinarith
  have hX2 : beta ε * (u * (u + 2)) ≤ X := by
    have : beta ε * (u * (u + 2)) ≤ (u - 1) * (u * (u + 2)) :=
      mul_le_mul_of_nonneg_right hu1 (by positivity)
    linarith
  have h9 : 9 * (u * (u + 2)) ≤ 9 / beta ε * X := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hb]; nlinarith
  have h6 : 6 * ((u - 1) * (u * (u + 2))) ≤ 6 * X := by linarith
  nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ u - 1) (by linarith : (0:ℝ) ≤ u)) (by linarith : (0:ℝ) ≤ u)]

