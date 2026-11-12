-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja21_original_cutoff_gaussian_measurable_square_moment_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T14:52:04.299983+00:00
-- url     : https://prove2.me/submissions/26346f2a-31f0-42b5-93cd-0ec346c0de5b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_cutoff_residual_gaussian_core_split
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_gaussian_core_and_jump_cutoff_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_finite_activity_smallband_cutoff_square_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_fixed_gaussian_core_second_moment
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_compensated_smallband_exact_variance
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_gaussian_core_smallband_orthogonal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (t : ℝ≥0),
      ∃ (G J : Ω → ℝ),
        (∀ᵐ ω ∂P,
          avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω = G ω + J ω) ∧
        AEStronglyMeasurable G P ∧
        AEStronglyMeasurable J P ∧
        Integrable (fun ω => (G ω) ^ 2) P ∧
        Integrable (fun ω => (J ω) ^ 2) P ∧
        (∫ ω, G ω * J ω ∂P) = 0 ∧
        (∫ ω, (G ω) ^ 2 ∂P) = (t : ℝ) * X.σ ^ 2 ∧
        (∫ ω, (J ω) ^ 2 ∂P) =
          (t : ℝ) * (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν) := by
  intro n t
  let G : Ω → ℝ := fun ω =>
    avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω +
      avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω
  let J : Ω → ℝ := fun ω =>
    -avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω
  obtain ⟨hGMeas, hJMeas⟩ :=
    avram_ja21_original_gaussian_core_and_jump_cutoff_measurable X n t
  obtain ⟨hGsq, hGmom⟩ :=
    avram_ja21_original_fixed_gaussian_core_second_moment X hX hFinite t
  have hJsq : Integrable (fun ω => (J ω) ^ 2) P := by
    simpa only [J, Pi.neg_apply, neg_sq] using
      (avram_ja21_original_finite_activity_smallband_cutoff_square_integrable
        X hFinite n t)
  refine ⟨G, J, ?_, ?_, ?_, ?_, hJsq, ?_, ?_, ?_⟩
  · filter_upwards [] with ω
    simpa only [G, J, sub_eq_add_neg] using
      (avram_ja21_original_cutoff_residual_gaussian_core_split X n t ω)
  · exact (hGMeas.mono (𝓕.le t) le_rfl).aestronglyMeasurable
  · exact (hJMeas.mono (𝓕.le t) le_rfl).aestronglyMeasurable
  · simpa only [G] using hGsq
  · exact avram_ja21_original_gaussian_core_smallband_orthogonal
      X hX hFinite n t
  · simpa only [G] using hGmom
  · simpa only [J, Pi.neg_apply, neg_sq] using
      (avram_ja21_original_compensated_smallband_exact_variance
        X hX hFinite n t)
