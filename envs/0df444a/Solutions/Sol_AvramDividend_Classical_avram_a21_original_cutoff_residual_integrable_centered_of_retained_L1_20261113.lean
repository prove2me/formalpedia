-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_cutoff_residual_integrable_centered_of_retained_L1_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:50:38.204241+00:00
-- url     : https://prove2.me/submissions/285ee518-323e-4a99-a0c1-e9727777a317

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja18_zero_cutoff_fixed_time_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_intrinsic_gaussian_core_centered
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_smallband_cutoff_centered
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_residual_eq_zero_residual_sub_retained_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Source intrinsic residual centring follows from the true physical retained-band subtraction. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (t : ℝ≥0)
    (hJ : Integrable (fun ω =>
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) P) :
    Integrable (fun ω =>
      avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) P ∧
      (∫ ω,
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω ∂P) = 0 := by
  let Rn : Ω → ℝ := fun ω =>
    avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω
  let R0 : Ω → ℝ := fun ω =>
    avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω
  let Jn : Ω → ℝ := fun ω =>
    avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω
  have hR0 : Integrable R0 P :=
    avram_ja18_zero_cutoff_fixed_time_integrable X hX hFinite t
  have hR0Center : (∫ ω, R0 ω ∂P) = 0 := by
    simpa only [avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff,
      add_zero] using
      (avram_ja21_original_intrinsic_gaussian_core_centered X hX hFinite t)
  have hJCenter : (∫ ω, Jn ω ∂P) = 0 := by
    have h := avram_ja21_original_smallband_cutoff_centered X hX hFinite n t
    simpa only [integral_neg, neg_eq_zero] using h
  have hPath : Rn = fun ω => R0 ω - Jn ω := by
    funext ω
    exact avram_a21_original_residual_eq_zero_residual_sub_retained_20261113
      X n t ω
  have hRn : Integrable Rn P := by
    rw [hPath]
    exact hR0.sub hJ
  have hInt : (∫ ω, Rn ω ∂P) = 0 := by
    rw [hPath, integral_sub hR0 hJ, hR0Center, hJCenter, sub_zero]
  exact ⟨hRn, hInt⟩
