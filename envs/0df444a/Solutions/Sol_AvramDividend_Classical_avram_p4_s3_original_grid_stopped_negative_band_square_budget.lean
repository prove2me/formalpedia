-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_grid_stopped_negative_band_square_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T08:54:43.895697+00:00
-- url     : https://prove2.me/submissions/04b4bd64-3f1c-4327-a5ac-6aa6bcff659f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_grid_selected_negative_band_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_stop_negative_band_square_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Quantitative second-moment control at every bounded measurable grid clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (tick : Ω → ℕ) (htick : Measurable tick)
    (grid : ℕ → ℝ≥0) (hgrid : ∀ ω, grid (tick ω) ≤ T) :
    let K : Ω → ℕ := fun ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ grid (tick ω) ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => (K ω : ℝ) ^ 2) P ∧
      (∫ ω, (K ω : ℝ) ^ 2 ∂P) ≤ r ^ 2 + r := by
  exact
    avram_p4_s3_original_bounded_stop_negative_band_square_budget
      X T n (fun ω => grid (tick ω)) hgrid
      (avram_p4_s3_original_grid_selected_negative_band_count_measurable
        X n tick htick grid)
