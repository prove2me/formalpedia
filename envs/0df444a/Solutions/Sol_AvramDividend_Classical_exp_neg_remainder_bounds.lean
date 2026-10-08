-- Prove2me | solution 1 for AvramDividend.Classical.exp_neg_remainder_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T15:48:03.303983+00:00
-- url     : https://prove2.me/submissions/e37933ca-e5b0-4f2e-9cab-5a9d3a60c1f0

import Mathlib

theorem solution (z : ℝ) (hz : z ≤ 0) :
    0 ≤ Real.exp z - 1 - z ∧ Real.exp z - 1 - z ≤ z ^ 2 := by
  constructor
  · linarith [Real.add_one_le_exp z]
  · by_cases hnear : -1 ≤ z
    · have hzabs : |z| ≤ 1 := abs_le.mpr ⟨hnear, by linarith⟩
      exact (le_abs_self _).trans (Real.abs_exp_sub_one_sub_id_le hzabs)
    · have hfar : z ≤ -1 := le_of_not_ge hnear
      have hexp : Real.exp z ≤ 1 := Real.exp_le_one_iff.mpr hz
      have hprod : 0 ≤ (-z) * (-z - 1) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith [hprod]
