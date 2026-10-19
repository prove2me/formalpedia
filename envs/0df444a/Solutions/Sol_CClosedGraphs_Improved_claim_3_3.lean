-- Prove2me | solution 1 for CClosedGraphs.Improved.claim_3_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-18T19:58:36.84008+00:00
-- url     : https://prove2.me/submissions/e0067110-7e20-406d-b1db-befefd265e37

import Mathlib
set_option autoImplicit false

theorem solution (x k : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1 / 2) (hk1 : 1 ≤ k) (hk2 : k ≤ 2) :
    (1 - x) ^ k ≤ 1 - x * k / 2 := by
  have ha : 0 < 1 - x := by linarith
  have h := convexOn_exp.2 (Set.mem_univ (Real.log (1 - x))) (Set.mem_univ (2 * Real.log (1 - x)))
    (show (0:ℝ) ≤ 2 - k by linarith) (show (0:ℝ) ≤ k - 1 by linarith) (by ring)
  have e1 : (1 - x) ^ k = Real.exp ((2 - k) • Real.log (1 - x) + (k - 1) • (2 * Real.log (1 - x))) := by
    rw [Real.rpow_def_of_pos ha]
    congr 1
    simp only [smul_eq_mul]; ring
  have e2 : Real.exp (2 * Real.log (1 - x)) = (1 - x) ^ 2 := by
    rw [show 2 * Real.log (1 - x) = Real.log (1 - x) + Real.log (1 - x) by ring, Real.exp_add,
      Real.exp_log ha]; ring
  rw [e1]
  refine h.trans ?_
  simp only [smul_eq_mul, Real.exp_log ha, e2]
  nlinarith [mul_nonneg (sub_nonneg.2 hk1) hx0.le, mul_nonneg (mul_nonneg (sub_nonneg.2 hk1) hx0.le) (sub_nonneg.2 hx1),
    mul_nonneg hx0.le (sub_nonneg.2 hx1)]
