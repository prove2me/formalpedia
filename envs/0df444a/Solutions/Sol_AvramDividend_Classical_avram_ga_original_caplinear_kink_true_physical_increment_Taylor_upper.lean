-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_original_caplinear_kink_true_physical_increment_Taylor_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T22:41:21.779962+00:00
-- url     : https://prove2.me/submissions/200bec72-31fc-4c91-b2a2-39e71ddee0fa

import Mathlib.Analysis.Calculus.Deriv.Basic
open Set
noncomputable section

theorem solution
    (w : ℝ → ℝ) (b α y z : ℝ) (hα : 1 ≤ α) :
    ((if y + z ≤ b then w (y + z) else w b + (y + z - b)) -
      (if y ≤ b then w y else w b + (y - b)) -
        (if y ≤ b then deriv w y else 1) * z) ≤
    ((if y + z ≤ b then w (y + z) else w b + α * (y + z - b)) -
      (if y ≤ b then w y else w b + α * (y - b)) -
        (if y ≤ b then deriv w y else α) * z) := by
  by_cases hy : y ≤ b
  · by_cases hz : y + z ≤ b
    · simp only [if_pos hy, if_pos hz]
      exact le_refl _
    · have hpos : 0 ≤ y + z - b := by linarith [lt_of_not_ge hz]
      have hneg : 1 - α ≤ 0 := by linarith
      have hmul : (1 - α) * (y + z - b) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hneg hpos
      simp only [if_pos hy, if_neg hz]
      nlinarith [hmul]
  · by_cases hz : y + z ≤ b
    · have hneg : y + z - b ≤ 0 := by linarith
      have hpos : 0 ≤ α - 1 := by linarith
      have hmul : (α - 1) * (y + z - b) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hpos hneg
      simp only [if_neg hy, if_pos hz]
      nlinarith [hmul]
    · simp only [if_neg hy, if_neg hz]
      nlinarith
