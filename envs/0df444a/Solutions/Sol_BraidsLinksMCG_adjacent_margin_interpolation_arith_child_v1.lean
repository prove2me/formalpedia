-- Prove2me | solution 1 for BraidsLinksMCG.adjacent_margin_interpolation_arith_child_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-23T17:16:19.040286+00:00
-- url     : https://prove2.me/submissions/37bc1196-94f0-404b-ad09-6be84c3e348d

import Mathlib

theorem solution (n : ℕ) (c r s : ℝ)
    (hsource : (n : ℝ) + 1 / 4 ≤ c - r / 2)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (n : ℝ) + 1 / 4 ≤ (1 - s) * c + s * ((n : ℝ) + 3 / 2) -
      ((1 - s) * r + s) / 2 := by
  have hfactor : 0 ≤ 1 - s := by linarith
  have hsource' := mul_le_mul_of_nonneg_left hsource hfactor
  have htarget' : s * ((n : ℝ) + 1 / 4) ≤ s * ((n : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left (by norm_num) hs0
  calc
    (n : ℝ) + 1 / 4 =
        (1 - s) * ((n : ℝ) + 1 / 4) + s * ((n : ℝ) + 1 / 4) := by ring
    _ ≤ (1 - s) * (c - r / 2) + s * ((n : ℝ) + 1) :=
      add_le_add hsource' htarget'
    _ = (1 - s) * c + s * ((n : ℝ) + 3 / 2) -
          ((1 - s) * r + s) / 2 := by ring
