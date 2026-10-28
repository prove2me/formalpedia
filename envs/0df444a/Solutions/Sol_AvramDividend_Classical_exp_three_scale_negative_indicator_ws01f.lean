-- Prove2me | solution 1 for AvramDividend.Classical.exp_three_scale_negative_indicator_ws01f
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T10:32:45.728763+00:00
-- url     : https://prove2.me/submissions/bd46b5d7-725e-4297-a0e1-62ebb7d9f79b

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false

open Filter

theorem solution (r x : ℝ) (hr : 1 ≤ r) :
    Real.exp x - 1 ≤
      r ^ 2 * (Real.exp (x / r) - 1) +
      (Real.exp (2 * x) - 1) / r +
      (r ^ 2 + 1 / r) * (if x < 0 then (1 : ℝ) else 0) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
  by_cases hx : x < 0
  · have hex : Real.exp x ≤ 1 := Real.exp_le_one_iff.mpr hx.le
    have ha : 0 ≤ r ^ 2 * Real.exp (x / r) :=
      mul_nonneg hr2 (Real.exp_pos _).le
    have hb : 0 ≤ Real.exp (2 * x) / r :=
      div_nonneg (Real.exp_pos _).le hr0.le
    have heq :
        r ^ 2 * (Real.exp (x / r) - 1) +
          (Real.exp (2 * x) - 1) / r + (r ^ 2 + 1 / r) =
          r ^ 2 * Real.exp (x / r) + Real.exp (2 * x) / r := by
      ring
    simp only [if_pos hx, mul_one]
    rw [heq]
    linarith
  · have hx0 : 0 ≤ x := le_of_not_gt hx
    have hdiv : 0 ≤ x / r := div_nonneg hx0 hr0.le
    have hsmall : 0 ≤ Real.exp (x / r) - 1 := by
      have h := Real.add_one_le_exp (x / r)
      linarith
    have hsmallprod : 0 ≤ r ^ 2 * (Real.exp (x / r) - 1) :=
      mul_nonneg hr2 hsmall
    have hdoubleNonneg : 0 ≤ (Real.exp (2 * x) - 1) / r := by
      apply div_nonneg _ hr0.le
      have h := Real.add_one_le_exp (2 * x)
      linarith
    simp only [if_neg hx, mul_zero, add_zero]
    by_cases hbound : Real.exp x ≤ r
    · have hnegexp := Real.add_one_le_exp (-x)
      have hmul :=
        mul_le_mul_of_nonneg_right hnegexp (Real.exp_pos x).le
      have hcancel : Real.exp (-x) * Real.exp x = 1 := by
        rw [Real.exp_neg]
        exact inv_mul_cancel₀ (ne_of_gt (Real.exp_pos x))
      have hlin : Real.exp x - 1 ≤ x * Real.exp x := by
        rw [hcancel] at hmul
        nlinarith [hmul]
      have hmx : x * Real.exp x ≤ r * x := by
        have h := mul_le_mul_of_nonneg_left hbound hx0
        nlinarith [h]
      have hfirst : r * x ≤ r ^ 2 * (Real.exp (x / r) - 1) := by
        have hh : x / r ≤ Real.exp (x / r) - 1 := by
          have he := Real.add_one_le_exp (x / r)
          linarith
        have hm := mul_le_mul_of_nonneg_left hh hr2
        have hid : r ^ 2 * (x / r) = r * x := by
          field_simp [ne_of_gt hr0] <;> ring
        calc
          r * x = r ^ 2 * (x / r) := hid.symm
          _ ≤ r ^ 2 * (Real.exp (x / r) - 1) := hm
      linarith
    · have hpositive : 0 ≤ Real.exp x - 1 := by
        have h := Real.add_one_le_exp x
        linarith
      have hdouble : Real.exp (2 * x) = Real.exp x * Real.exp x := by
        convert Real.exp_add x x using 1 <;> ring
      have hfactor : (Real.exp x - 1) * r ≤ Real.exp (2 * x) - 1 := by
        have hb : r ≤ Real.exp x + 1 := by
          have hp : r < Real.exp x := lt_of_not_ge hbound
          linarith
        calc
          (Real.exp x - 1) * r ≤
              (Real.exp x - 1) * (Real.exp x + 1) :=
                mul_le_mul_of_nonneg_left hb hpositive
          _ = Real.exp (2 * x) - 1 := by rw [hdouble]; ring
      have hsecond : Real.exp x - 1 ≤
          (Real.exp (2 * x) - 1) / r :=
        (le_div_iff₀ hr0).mpr hfactor
      linarith
