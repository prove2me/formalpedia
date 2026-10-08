-- Prove2me | solution 2 for AvramDividend.Classical.exp_neg_sub_one_add_le_sq
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-06T17:37:33.19666+00:00
-- url     : https://prove2.me/submissions/3c9dcbc7-ca22-4784-91c6-320d37680aa4

import Mathlib

theorem solution (u : ℝ) (hu : 0 ≤ u) :
    Real.exp (-u) - 1 + u ≤ u ^ 2 := by
  rcases le_total u 1 with h | h
  · have h1 := Real.abs_exp_sub_one_sub_id_le (x := -u)
      (by rw [abs_neg, abs_of_nonneg hu]; exact h)
    have h2 := (abs_le.mp h1).2
    nlinarith [h2]
  · have h3 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith
