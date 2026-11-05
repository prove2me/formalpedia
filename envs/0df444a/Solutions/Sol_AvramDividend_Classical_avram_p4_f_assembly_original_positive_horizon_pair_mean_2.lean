-- Prove2me | solution 2 for AvramDividend.Classical.avram_p4_f_assembly_original_positive_horizon_pair_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T18:54:04.099419+00:00
-- url     : https://prove2.me/submissions/7c4bfbc5-fe1d-4695-a4ae-bb3e957da9ca

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_pair_mean_two_source_gaps
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_physical_ceil_pair_measurable_all_grid
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_expected_ceil_pair_tendsto
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical Filter
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let K : Ω → ℕ := fun ω =>
      ((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card
    let r : ℝ :=
      (((T : ℝ≥0) : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => 2 * (K ω : ℝ)) P ∧
    (∫ ω, 2 * (K ω : ℝ) ∂P) = r ^ 2  := by
  exact avram_p4_f_assembly_original_pair_mean_two_source_gaps
    X T hT n
    (avram_p4_f_assembly_original_physical_ceil_pair_measurable_all_grid
      X T hT n)
    (avram_p4_f_assembly_original_expected_ceil_pair_tendsto
      X T hT n)
