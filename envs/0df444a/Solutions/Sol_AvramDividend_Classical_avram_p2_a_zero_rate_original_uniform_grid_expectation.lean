-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_original_uniform_grid_expectation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:57:52.006086+00:00
-- url     : https://prove2.me/submissions/1c27a66a-4d88-4b8f-9cd6-6908b99bcc5d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_borel_marked_grid_mean_sum_of_stationary_cell_probabilities
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_grid_probability_sum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

/-- Exact genuine-source first moment of the uniform marked grid,
using stationary increments and its proved common duration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ) (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω, ∑ j ∈ Finset.range (n + 1),
      B.indicator (fun _ : ℝ => (1 : ℝ≥0∞))
        (X.X (((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
         X.X ((j : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω) ∂P) =
    (((n + 1 : ℕ) : ℝ≥0∞) * P {ω : Ω | X.X (T / ((n : ℝ≥0) + 1)) ω ∈ B}) := by
  classical
  let δ : ℝ≥0 := T / ((n : ℝ≥0) + 1)
  let grid : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * δ
  have hGrid : ∀ i : ℕ, i < n + 1 → grid i ≤ grid (i + 1) := by
    intro i hi
    dsimp [grid]
    gcongr
    exact Nat.le_succ i
  have hMean :=
    avram_wave6_01_original_borel_marked_grid_mean_sum_of_stationary_cell_probabilities
      X 0 (n + 1) grid hGrid B hB
  calc
    (∫⁻ ω, ∑ j ∈ Finset.range (n + 1),
      B.indicator (fun _ : ℝ => (1 : ℝ≥0∞))
        (X.X (((j + 1 : ℕ) : ℝ≥0) * δ) ω -
         X.X ((j : ℝ≥0) * δ) ω) ∂P) =
      ∑ j ∈ Finset.range (n + 1),
        P {ω : Ω | X.X (((((j + 1 : ℕ) : ℝ≥0) * δ) -
          ((j : ℝ≥0) * δ))) ω ∈ B} := by
            simpa only [zero_add, grid] using hMean
    _ = (((n + 1 : ℕ) : ℝ≥0∞) * P {ω : Ω | X.X δ ω ∈ B}) := by
      simpa only [δ] using
        (avram_p2_a_zero_rate_uniform_grid_probability_sum X T n B)
    _ = _ := by rfl
