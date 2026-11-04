-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_uniform_grid_probability_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:56:24.487067+00:00
-- url     : https://prove2.me/submissions/cb40929e-b48f-423f-8254-6d0146e72aa5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_cell_width

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The original uniform finite grid has one identical source-duration
probability term per cell, with ENNReal arithmetic. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ) (B : Set ℝ) :
    (∑ j ∈ Finset.range (n + 1),
      P {ω : Ω | X.X (((((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
        ((j : ℝ≥0) * (T / ((n : ℝ≥0) + 1))))) ω ∈ B}) =
    (((n + 1 : ℕ) : ℝ≥0∞) * P {ω : Ω | X.X (T / ((n : ℝ≥0) + 1)) ω ∈ B}) := by
  classical
  let δ : ℝ≥0 := T / ((n : ℝ≥0) + 1)
  calc
    (∑ j ∈ Finset.range (n + 1),
      P {ω : Ω | X.X (((((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
        ((j : ℝ≥0) * (T / ((n : ℝ≥0) + 1))))) ω ∈ B}) =
      ∑ j ∈ Finset.range (n + 1), P {ω : Ω | X.X δ ω ∈ B} := by
        apply Finset.sum_congr rfl
        intro j hj
        simpa only [δ] using
          (congrArg (fun t : Set Ω => P t)
            (show {ω : Ω | X.X (((((j + 1 : ℕ) : ℝ≥0) * δ) -
                ((j : ℝ≥0) * δ))) ω ∈ B} =
              {ω : Ω | X.X δ ω ∈ B} from by
                simp only [avram_p2_a_zero_rate_uniform_cell_width]))
    _ = (((n + 1 : ℕ) : ℝ≥0∞) * P {ω : Ω | X.X δ ω ∈ B}) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = _ := by rfl
