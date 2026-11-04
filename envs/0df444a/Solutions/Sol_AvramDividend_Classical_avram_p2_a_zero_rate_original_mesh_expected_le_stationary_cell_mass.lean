-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_original_mesh_expected_le_stationary_cell_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T14:48:09.197378+00:00
-- url     : https://prove2.me/submissions/c0be8917-131f-4c7d-a7c6-f99e919cb70d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_mesh_count_le_cell_indicators
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_borel_marked_grid_mean_sum_of_stationary_cell_probabilities

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

/-- Expected original image-grid occupancy is bounded by its genuine
stationary source-cell probability mass on the same sample space. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ) (ε : ℝ) :
    (∫⁻ ω, (((((Finset.range (n + 1)).image
      (fun j : ℕ => ((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))).filter
      (fun t : ℝ≥0 => X.X t ω -
        X.X (t - (T / ((n : ℝ≥0) + 1))) ω < -ε / 2)).card : ℕ) : ℝ≥0∞) ∂P) ≤
    ∑ j ∈ Finset.range (n + 1),
      P {v : Ω |
        X.X ((((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
          ((j : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))) v ∈ Iio (-ε / 2)} := by
  classical
  letI : DecidableEq ℝ≥0 := Classical.decEq _
  let δ : ℝ≥0 := T / ((n : ℝ≥0) + 1)
  let grid : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * δ
  let B : Set ℝ := Iio (-ε / 2)
  have hGrid : ∀ i : ℕ, i < n + 1 → grid i ≤ grid (i + 1) := by
    intro i hi
    dsimp [grid]
    gcongr
    exact Nat.le_succ i
  have hMean :=
    avram_wave6_01_original_borel_marked_grid_mean_sum_of_stationary_cell_probabilities
      X 0 (n + 1) grid hGrid B (by simpa only [B] using measurableSet_Iio)
  calc
    (∫⁻ ω, (((((Finset.range (n + 1)).image
      (fun j : ℕ => ((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))).filter
      (fun t : ℝ≥0 => X.X t ω -
        X.X (t - (T / ((n : ℝ≥0) + 1))) ω < -ε / 2)).card : ℕ) : ℝ≥0∞) ∂P) ≤
        (∫⁻ ω, ∑ j ∈ Finset.range (n + 1),
          ({v : Ω | X.X (((j + 1 : ℕ) : ℝ≥0) * δ) v -
            X.X ((j : ℝ≥0) * δ) v < -ε / 2}).indicator
            (fun _ : Ω => (1 : ℝ≥0∞)) ω ∂P) := by
      apply MeasureTheory.lintegral_mono
      intro ω
      simpa only [δ] using
        (avram_p2_a_zero_rate_original_mesh_count_le_cell_indicators X ω T n ε)
    _ = (∫⁻ ω, ∑ j ∈ Finset.range (n + 1),
        B.indicator (fun _ : ℝ => (1 : ℝ≥0∞))
          (X.X (grid (j + 1)) ω - X.X (grid j) ω) ∂P) := by
      congr 1
    _ = ∑ j ∈ Finset.range (n + 1),
      P {v : Ω |
        X.X ((((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
          ((j : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))) v ∈ Iio (-ε / 2)} := by
      simpa only [zero_add, B, grid, δ] using hMean
