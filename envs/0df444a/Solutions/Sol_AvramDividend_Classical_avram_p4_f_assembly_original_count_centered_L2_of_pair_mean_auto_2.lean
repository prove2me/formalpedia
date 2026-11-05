-- Prove2me | solution 2 for AvramDividend.Classical.avram_p4_f_assembly_original_count_centered_L2_of_pair_mean_auto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:42:47.070592+00:00
-- url     : https://prove2.me/submissions/565ebdb2-ca8e-4062-8307-c06d051af9ed

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_centered_count_l2_pair_rate
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cutoff_marked_count_L1_auto
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cutoff_marked_count_real_mean_auto
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let J : Ω → ℝ := fun ω =>
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1))))).toReal
    let K : Ω → ℕ := fun ω =>
      ((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card
    let r : ℝ :=
      (((T : ℝ≥0) : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => 2 * (K ω : ℝ)) P →
    (∫ ω, 2 * (K ω : ℝ) ∂P) = r ^ 2 →
    Integrable (fun ω => (J ω - r) ^ 2) P ∧
    (∫ ω, (J ω - r) ^ 2 ∂P) = r := by
  dsimp only
  intro hK hKmean
  exact avram_p4_f_assembly_original_centered_count_l2_pair_rate X T n
    (avram_p4_f_assembly_original_cutoff_marked_count_L1_auto X T n)
    (avram_p4_f_assembly_original_cutoff_marked_count_real_mean_auto X T n)
    hK hKmean
