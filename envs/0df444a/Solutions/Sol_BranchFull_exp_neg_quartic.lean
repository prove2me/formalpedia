-- Prove2me | solution 1 for BranchFull.exp_neg_quartic
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T05:38:11.601346+00:00
-- url     : https://prove2.me/submissions/aa6b2bd5-7e53-4471-8cb0-c8d9f51befd8

import Mathlib
theorem solution (y : ℝ) (hy : 0 < y) :
    Real.exp (-y) ≤ 24 / y^4 := by
  have h := Real.pow_div_factorial_le_exp y hy.le 4
  norm_num at h
  rw [Real.exp_neg]
  rw [← one_div (Real.exp y)]
  apply (div_le_div_iff₀ (Real.exp_pos y) (pow_pos hy 4)).2
  nlinarith