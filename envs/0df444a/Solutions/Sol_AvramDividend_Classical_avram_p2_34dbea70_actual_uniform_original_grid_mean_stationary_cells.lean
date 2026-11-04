-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_actual_uniform_original_grid_mean_stationary_cells
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:02:22.467522+00:00
-- url     : https://prove2.me/submissions/bf42c339-9e35-4a28-8d61-2cf958e79e60

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_borel_marked_grid_mean_sum_of_stationary_cell_probabilities
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_uniform_original_grid_adjacent_duration

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The source original-process finite-grid mean becomes one identical
one-time increment probability per cell on an actual uniform time mesh. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ) (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω, ∑ i ∈ Finset.range (n + 1),
      B.indicator (fun _ : ℝ => (1 : ℝ≥0∞))
        (X.X (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
          X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω) ∂P) =
    ∑ _i ∈ Finset.range (n + 1),
      P {ω : Ω | X.X (T / ((n : ℝ≥0) + 1)) ω ∈ B} := by
  let grid : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))
  have hGrid : ∀ i : ℕ, i < n + 1 → grid i ≤ grid (i + 1) := by
    intro i _hi
    dsimp [grid]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ i) (by positivity)
  have hsource :=
    avram_wave6_01_original_borel_marked_grid_mean_sum_of_stationary_cell_probabilities
      X 0 (n + 1) grid hGrid B hB
  have hsource' :
      (∫⁻ ω, ∑ i ∈ Finset.range (n + 1),
        B.indicator (fun _ : ℝ => (1 : ℝ≥0∞))
          (X.X (grid (i + 1)) ω - X.X (grid i) ω) ∂P) =
      ∑ i ∈ Finset.range (n + 1),
        P {ω : Ω | X.X (grid (i + 1) - grid i) ω ∈ B} := by
    simpa only [zero_add] using hsource
  simpa only [grid, avram_p2_34dbea70_uniform_original_grid_adjacent_duration]
    using hsource'
