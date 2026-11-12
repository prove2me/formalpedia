-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a25_discounted_spatial_positive_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T00:35:32.623042+00:00
-- url     : https://prove2.me/submissions/b2c45ce5-174d-4b7f-8721-404539b3a9fc

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.SetSemiring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (m n : ℕ) (ρ : ℝ≥0) (q : ℝ) (R : ℕ → ℝ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
    let E : ℕ → ℝ := fun i => Real.exp (-(q * (v i : ℝ)))
    max (∑ i ∈ Finset.range (m + 1), E i * R i) 0 ≤
      ∑ i ∈ Finset.range (m + 1), E i * max (R i) 0 := by
  dsimp only
  apply max_le
  · apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (le_max_left (R i) 0) (Real.exp_pos _).le
  · apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (Real.exp_pos _).le (le_max_right (R i) 0)
