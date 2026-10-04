-- Prove2me | solution 1 for BalcanDDA.Piecewise.lemmaA_1_log_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T07:54:29.856255+00:00
-- url     : https://prove2.me/submissions/682996d4-2559-4d20-9629-03fae8496c85

import Mathlib

theorem solution (a b y : ℝ) (ha : 1 ≤ a) (hb : 0 < b)
    (hy : y < a * Real.log y + b) :
    y < 4 * a * Real.log (2 * a) + 2 * b := by
  by_contra h0
  have h := not_lt.mp h0
  have ha0 : 0 < a := by linarith
  have h2a : 0 < 2 * a := by linarith
  have hl2 : 0 < Real.log (2 * a) := Real.log_pos (by linarith)
  have haL : 0 ≤ a * Real.log (2 * a) := mul_nonneg ha0.le hl2.le
  have hy0 : 0 < y := by linarith
  have hlog : Real.log y = Real.log (2 * a) + Real.log (y / (2 * a)) := by
    rw [Real.log_div hy0.ne' h2a.ne']; ring
  have hle : Real.log (y / (2 * a)) ≤ y / (2 * a) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hy0 h2a)
  have key : a * Real.log (y / (2 * a)) ≤ y / 2 - a := by
    have h1 := mul_le_mul_of_nonneg_left hle ha0.le
    have e : a * (y / (2 * a) - 1) = y / 2 - a := by
      field_simp
    linarith
  have hy' : y < a * Real.log (2 * a) + a * Real.log (y / (2 * a)) + b := by
    rw [hlog, mul_add] at hy; exact hy
  linarith
