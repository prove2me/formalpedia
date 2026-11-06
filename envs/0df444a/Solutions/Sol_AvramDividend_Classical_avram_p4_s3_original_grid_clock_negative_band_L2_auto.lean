-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_grid_clock_negative_band_L2_auto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:26:46.645188+00:00
-- url     : https://prove2.me/submissions/f412ae20-b532-42d2-9790-0415dac18220

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

/-- Genuine original negative-band counts at measurable grid clocks lie in L². -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (tick : Ω → ℕ) (htick : Measurable tick)
    (grid : ℕ → ℝ≥0) (hgrid : ∀ ω, grid (tick ω) ≤ T) :
    MemLp (fun ω : Ω => ({u : ℝ≥0 | 0 < u ∧
      u ≤ grid (tick ω) ∧
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
      X T n tick htick grid hgrid).1
  have hKr : Measurable (fun ω => (K ω : ℝ)) :=
    (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp hKm
  exact (memLp_two_iff_integrable_sq hKr.aestronglyMeasurable).2 hK2
