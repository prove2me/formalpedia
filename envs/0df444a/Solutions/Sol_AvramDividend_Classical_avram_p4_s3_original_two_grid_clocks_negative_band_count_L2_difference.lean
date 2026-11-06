-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_two_grid_clocks_negative_band_count_L2_difference
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:28:37.550888+00:00
-- url     : https://prove2.me/submissions/019e03c4-c881-484f-b1df-9039b062b4f7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_grid_stopped_negative_band_square_budget
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_grid_selected_negative_band_count_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Two true original jump-count localisations have square-integrable differences. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (grid : ℕ → ℝ≥0)
    (tick₁ tick₂ : Ω → ℕ)
    (htick₁ : Measurable tick₁) (htick₂ : Measurable tick₂)
    (hbound₁ : ∀ ω, grid (tick₁ ω) ≤ T)
    (hbound₂ : ∀ ω, grid (tick₂ ω) ≤ T) :
    MemLp (fun ω : Ω =>
      ({u : ℝ≥0 | 0 < u ∧ u ≤ grid (tick₁ ω) ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard : ℝ) -
      ({u : ℝ≥0 | 0 < u ∧ u ≤ grid (tick₂ ω) ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard : ℝ)) 2 P := by
  have hClock (tick : Ω → ℕ) (htick : Measurable tick)
      (hbound : ∀ ω, grid (tick ω) ≤ T) :
      MemLp (fun ω : Ω =>
        ({u : ℝ≥0 | 0 < u ∧ u ≤ grid (tick ω) ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
            -(1 / ((n : ℝ) + 1))}.ncard : ℝ)) 2 P := by
    let K : Ω → ℕ := fun ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ grid (tick ω) ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    change MemLp (fun ω => (K ω : ℝ)) 2 P
    have hKm : Measurable K :=
      avram_p4_s3_original_grid_selected_negative_band_count_measurable
        X n tick htick grid
    have hK2 : Integrable (fun ω => (K ω : ℝ) ^ 2) P :=
      (avram_p4_s3_original_grid_stopped_negative_band_square_budget
        X T n tick htick grid hbound).1
    have hKr : Measurable (fun ω => (K ω : ℝ)) :=
      (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp hKm
    exact (memLp_two_iff_integrable_sq hKr.aestronglyMeasurable).2 hK2
  exact (hClock tick₁ htick₁ hbound₁).sub (hClock tick₂ htick₂ hbound₂)
