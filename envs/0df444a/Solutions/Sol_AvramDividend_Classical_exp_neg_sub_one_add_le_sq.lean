-- Prove2me | solution 1 for AvramDividend.Classical.exp_neg_sub_one_add_le_sq
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-06T17:22:38.990977+00:00
-- url     : https://prove2.me/submissions/a1c888e9-f913-46b2-afc0-54302c5c2e38

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
