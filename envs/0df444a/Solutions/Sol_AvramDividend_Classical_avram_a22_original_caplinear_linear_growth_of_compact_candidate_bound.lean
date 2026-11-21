-- Prove2me | solution 1 for AvramDividend.Classical.avram_a22_original_caplinear_linear_growth_of_compact_candidate_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:20:40.149737+00:00
-- url     : https://prove2.me/submissions/5bcf7782-fe7a-41d6-9f85-8d4773b332b7

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution
    (w : ℝ → ℝ) (b K : ℝ) (hb : 0 ≤ b) (hK : 0 ≤ K)
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0)
    (hw_bound : ∀ z : ℝ, 0 ≤ z → z ≤ b → |w z| ≤ K)
    (z : ℝ) :
    |if z ≤ b then w z else w b + (z - b)| ≤ K + |z|  := by
  by_cases hzcap : z ≤ b
  · simp only [if_pos hzcap]
    by_cases hzneg : z < 0
    · rw [hw_neg z hzneg]
      simp only [abs_zero]
      linarith [abs_nonneg z]
    · have hz0 : 0 ≤ z := le_of_not_gt hzneg
      have hwb := hw_bound z hz0 hzcap
      linarith [abs_nonneg z]
  · simp only [if_neg hzcap]
    have hzb : b < z := lt_of_not_ge hzcap
    have hwb : |w b| ≤ K := hw_bound b hb le_rfl
    have hz0 : 0 ≤ z := le_trans hb (le_of_lt hzb)
    have hd0 : 0 ≤ z - b := by linarith
    rw [abs_of_nonneg hz0]
    have htri := abs_add_le (w b) (z - b)
    rw [abs_of_nonneg hd0] at htri
    linarith
