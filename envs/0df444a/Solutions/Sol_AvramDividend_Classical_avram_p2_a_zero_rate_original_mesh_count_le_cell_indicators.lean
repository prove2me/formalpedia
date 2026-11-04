-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_original_mesh_count_le_cell_indicators
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:22:31.993277+00:00
-- url     : https://prove2.me/submissions/183cc766-6d13-4ea3-8096-f6636b595d33

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_image_count_le_indicator_sum
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_cell_predecessor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

/-- On the actual original process, a finite negative image-mesh count is
bounded by the ENNReal occupancy sum over its source-cell indices. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0) (n : ℕ) (ε : ℝ) :
    (((((Finset.range (n + 1)).image
      (fun j : ℕ => ((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))).filter
      (fun t : ℝ≥0 => X.X t ω -
        X.X (t - (T / ((n : ℝ≥0) + 1))) ω < -ε / 2)).card : ℕ) : ℝ≥0∞) ≤
    ∑ j ∈ Finset.range (n + 1),
      ({v : Ω | X.X (((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) v -
        X.X ((j : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) v < -ε / 2}).indicator
        (fun _ : Ω => (1 : ℝ≥0∞)) ω := by
  classical
  let δ : ℝ≥0 := T / ((n : ℝ≥0) + 1)
  have h := avram_p2_a_zero_rate_image_count_le_indicator_sum
    (Finset.range (n + 1))
    (fun j : ℕ => ((j + 1 : ℕ) : ℝ≥0) * δ)
    (fun t : ℝ≥0 => X.X t ω - X.X (t - δ) ω < -ε / 2)
  convert h using 1
  · congr 1
    congr 1
    apply Finset.ext
    intro t
    simp only [Finset.mem_filter, Finset.mem_image, δ]
  · apply Finset.sum_congr rfl
    intro j hj
    by_cases hp : X.X (((j + 1 : ℕ) : ℝ≥0) * δ) ω -
        X.X ((j : ℝ≥0) * δ) ω < -ε / 2
    · simp [δ, Set.indicator, Nat.cast_add, Nat.cast_one, add_mul,
        add_tsub_cancel_right, avram_p2_a_zero_rate_uniform_cell_predecessor, hp]
    · simp [δ, Set.indicator, Nat.cast_add, Nat.cast_one, add_mul,
        add_tsub_cancel_right, avram_p2_a_zero_rate_uniform_cell_predecessor, hp]
