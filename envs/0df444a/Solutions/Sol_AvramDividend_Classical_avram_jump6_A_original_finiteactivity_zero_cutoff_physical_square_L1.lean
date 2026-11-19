-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_original_finiteactivity_zero_cutoff_physical_square_L1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T23:34:08.572833+00:00
-- url     : https://prove2.me/submissions/ebee6cd6-93f5-4717-bd6a-75e9dd5cc4dd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_ja22_original_limit_gaussian_exact_square_moment
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_intrinsic_limit_ae_rightCont_measurable_of_cutoffs
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
import Theorems.Thm_AvramDividend_Classical_avram_anoise21_original_gaussian_residual_L2_cutoff_error
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_square_integrable_of_limit_and_physical_error
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) :
    Integrable (fun ω =>
      (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 T ω) ^ 2) P := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  have hCut : ∀ (j : ℕ) (t : ℝ≥0),
      Measurable[𝓕.rightCont t]
        (fun ω : Ω => avram_p4_h_gaussian_intrinsic_truncated_residual X j t ω) := by
    intro j t
    exact (avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
      X j t).mono (𝓕.le_rightCont t) le_rfl
  obtain ⟨R, hRsrc, hRmeasAll⟩ :=
    avram_mix_gauss14_intrinsic_limit_ae_rightCont_measurable_of_cutoffs
      X hFinite hCut
  have hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun j : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X j t ω)
        atTop (nhds (R t ω)) := by
    filter_upwards [hRsrc] with ω hω
    exact hω.1
  have hRSq : Integrable (fun ω => (R T ω) ^ 2) P :=
    (avram_ja22_original_limit_gaussian_exact_square_moment
      X hX hFinite R hR T).1
  have hRsrcT : ∀ᵐ ω ∂P,
      Tendsto (fun j : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X j T ω)
        atTop (nhds (R T ω)) := by
    filter_upwards [hR] with ω hω
    exact hω T
  have hRmeas : AEStronglyMeasurable (R T) P :=
    (hRmeasAll T).mono ((𝓕.rightCont).le T)
  have hCutMeas : ∀ j : ℕ, AEStronglyMeasurable
      (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X j T ω) P := by
    intro j
    exact ((avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
      X j T).mono (𝓕.le T) le_rfl).aestronglyMeasurable
  let G : Ω → ℝ := fun ω =>
    avram_p4_h_gaussian_intrinsic_truncated_residual X 0 T ω
  let E : Ω → ℝ := fun ω => R T ω - G ω
  have hErr : Integrable (fun ω => E ω ^ 2) P := by
    simpa only [E, G] using
      (avram_anoise21_original_gaussian_residual_L2_cutoff_error
        X hFinite R T hRsrcT hRmeas hCutMeas 0).1
  change Integrable (fun ω => (G ω) ^ 2) P
  exact avram_jump6_A_square_integrable_of_limit_and_physical_error
    P (R T) G hRSq hErr (by simpa only [G] using hCutMeas 0)
