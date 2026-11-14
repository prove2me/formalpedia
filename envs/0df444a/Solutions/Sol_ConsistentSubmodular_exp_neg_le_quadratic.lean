-- Prove2me | solution 1 for ConsistentSubmodular.exp_neg_le_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:30:19.076605+00:00
-- url     : https://prove2.me/submissions/628a3497-b296-458a-82be-43c7853ba69c

import Mathlib

section

open scoped BigOperators

theorem solution {x : ℝ} (hx : 0 ≤ x) : Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  have hcubic : 1 + x + x ^ 2 / 2 + x ^ 3 / 6 ≤ Real.exp x := by
    have h := Real.sum_le_exp_of_nonneg hx 4
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_one,
      Nat.cast_ofNat, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMul, pow_zero, pow_one,
      zero_add, div_one] at h
    linarith
  have hprod : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos x
  have hA : 0 < 1 - x + x ^ 2 / 2 := by nlinarith [sq_nonneg (x - 1)]
  have hkey : 1 ≤ (1 - x + x ^ 2 / 2) * Real.exp x := by
    have hm := mul_le_mul_of_nonneg_left hcubic hA.le
    nlinarith [pow_nonneg hx 3, pow_nonneg hx 4, pow_nonneg hx 5]
  by_contra h
  have hlt := mul_lt_mul_of_pos_right (lt_of_not_ge h) hpos
  linarith

end
