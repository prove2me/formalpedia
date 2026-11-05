-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_original_negative_band_grid_eventually_injective
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:25:43.558598+00:00
-- url     : https://prove2.me/submissions/350aa69c-c024-4af0-a90a-8ee16577553c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_uniform_selected_cells_eventually_injective

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Separate the actual original-process negative-band jump times on fine source grids. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    ∀ (idx : ℝ≥0 → ℕ → ℕ),
      (∀ t ∈ F, ∀ k : ℕ,
        ((idx t k : ℕ) : ℝ≥0) * (T / ((k : ℝ≥0) + 1)) < t ∧
        t ≤ (((idx t k + 1 : ℕ) : ℝ≥0) *
          (T / ((k : ℝ≥0) + 1)))) →
      ∀ᶠ k : ℕ in Filter.atTop,
        Set.InjOn (fun t => idx t k) (F : Set ℝ≥0) := by
  intro F idx hcell
  exact avram_p2_a_zero_rate_original_uniform_selected_cells_eventually_injective
    T F idx hcell
