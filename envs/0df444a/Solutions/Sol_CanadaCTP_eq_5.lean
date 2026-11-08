-- Prove2me | solution 1 for CanadaCTP.eq_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:37:50.507202+00:00
-- url     : https://prove2.me/submissions/53b4ca0c-0967-45dc-a0ab-8b12889a2e89

import Mathlib

theorem solution (s : ℝ) (hs : 0 ≤ s) :
    (1 - Real.exp (-1)) * min 1 s ≤ 1 - Real.exp (-s) := by
  rcases le_total 1 s with h | h
  · rw [min_eq_left h]
    have : Real.exp (-s) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    linarith
  · rw [min_eq_right h]
    have key := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (-1:ℝ))
      (by linarith : (0:ℝ) ≤ 1 - s) hs (by ring)
    rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_zero, zero_add, Real.exp_zero,
      mul_one, show s * -1 = -s by ring] at key
    nlinarith
