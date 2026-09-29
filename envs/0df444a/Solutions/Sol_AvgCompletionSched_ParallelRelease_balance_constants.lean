-- Prove2me | solution 1 for AvgCompletionSched.ParallelRelease.balance_constants
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T21:52:52.711663+00:00
-- url     : https://prove2.me/submissions/b7057ac9-1943-4c76-af6e-ca2ab8c7d3d9

import Mathlib

theorem solution :
    2 + (2 * Real.sqrt 2 - 2) = 2 * Real.sqrt 2 ∧
      2 + Real.sqrt (3 - 2 * Real.sqrt 2) +
          (1 - (2 * Real.sqrt 2 - 2)) / Real.sqrt (3 - 2 * Real.sqrt 2) =
        2 * Real.sqrt 2 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hlt : (1:ℝ) < Real.sqrt 2 := by nlinarith
  have hkey : Real.sqrt (3 - 2 * Real.sqrt 2) = Real.sqrt 2 - 1 := by
    rw [show (3 - 2 * Real.sqrt 2 : ℝ) = (Real.sqrt 2 - 1) ^ 2 by nlinarith]
    exact Real.sqrt_sq (by linarith)
  have hne : Real.sqrt 2 - 1 ≠ 0 := by linarith
  have hfrac : (1 - (2 * Real.sqrt 2 - 2)) / (Real.sqrt 2 - 1) = Real.sqrt 2 - 1 := by
    rw [div_eq_iff hne]; nlinarith
  refine ⟨by ring, ?_⟩
  rw [hkey, hfrac]
  ring
