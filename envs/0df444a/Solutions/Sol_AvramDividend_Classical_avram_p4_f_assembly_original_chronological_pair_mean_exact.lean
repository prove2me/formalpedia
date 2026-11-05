-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_chronological_pair_mean_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T18:29:44.047211+00:00
-- url     : https://prove2.me/submissions/f3ee56fc-2f09-45c5-be5b-e47c5703f3f7

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_zero_horizon_pair_mean
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_positive_horizon_pair_mean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let K : Ω → ℕ := fun ω =>
      ((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card
    let r : ℝ :=
      (((T : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)
    Integrable (fun ω => 2 * (K ω : ℝ)) P ∧
    (∫ ω, 2 * (K ω : ℝ) ∂P) = r ^ 2 := by
  rcases eq_or_lt_of_le (show (0 : ℝ≥0) ≤ T from zero_le) with hzero | hpos
  · subst T
    exact avram_p4_f_assembly_original_zero_horizon_pair_mean X n
  · exact avram_p4_f_assembly_original_positive_horizon_pair_mean X T hpos n
