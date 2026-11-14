-- Prove2me | solution 5 for AvramDividend.Classical.avram_anoise22_original_gaussian_cutoff_exact_second_moment
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T13:19:12.822047+00:00
-- url     : https://prove2.me/submissions/2c2531fd-43c2-4922-a9c5-f0534862a2d7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_limit_rightCont_ae_adapted
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
import Theorems.Thm_AvramDividend_Classical_avram_ja22_original_limit_gaussian_exact_square_moment
import Theorems.Thm_AvramDividend_Classical_avram_ja22_original_omitted_nearzero_tail_exact_square_moment
import Theorems.Thm_AvramDividend_Classical_avram_ja22_original_limit_gaussian_omitted_tail_zero_cross
import Theorems.Thm_AvramDividend_Classical_avram_ja20_integrable_product_of_square_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ja19_square_integrable_of_ae_sum_components
import Theorems.Thm_AvramDividend_Classical_avram_ja20_integral_square_sum_uncorrelated
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- True physical finite-cutoff variance follows from Gaussian and omitted mark moments plus covariance zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (t : ℝ≥0),
      Integrable (fun ω =>
        (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) ^ 2) P ∧
      (∫ ω, (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) ^ 2 ∂P) =
        (t : ℝ) * X.σ ^ 2 +
          (t : ℝ) * (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν) := by
  obtain ⟨R, hLimit, hAdapt⟩ :=
    avram_mix_gauss14_original_intrinsic_limit_rightCont_ae_adapted X hFinite
  have hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (R t ω)) := by
    filter_upwards [hLimit] with ω hω
    exact hω.1
  intro n t
  let J : Ω → ℝ := fun ω =>
    avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω - R t ω
  have hGMeas : AEStronglyMeasurable (R t) P :=
    (hAdapt t).mono (𝓕.rightCont.le t)
  have hCutMeas : AEStronglyMeasurable
      (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) P :=
    ((avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
      X n t).mono (𝓕.le t) le_rfl).aestronglyMeasurable
  have hJMeas : AEStronglyMeasurable J P := hCutMeas.sub hGMeas
  have hG :=
    avram_ja22_original_limit_gaussian_exact_square_moment
      X hX hFinite R hR t
  have hJ :=
    avram_ja22_original_omitted_nearzero_tail_exact_square_moment
      X hX hFinite R hR n t
  have hCross :=
    avram_ja22_original_limit_gaussian_omitted_tail_zero_cross
      X hX hFinite R hR n t
  have hGJ : Integrable (fun ω => R t ω * J ω) P :=
    avram_ja20_integrable_product_of_square_integrable
      P (R t) J hGMeas hJMeas hG.1 hJ.1
  have hCutSq : Integrable
      (fun ω => (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) ^ 2) P := by
    apply avram_ja19_square_integrable_of_ae_sum_components
      (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
      (R t) J hCutMeas hG.1 hJ.1
    filter_upwards [] with ω
    dsimp [J]
    ring
  refine ⟨hCutSq, ?_⟩
  calc
    (∫ ω, (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) ^ 2 ∂P) =
        (∫ ω, (R t ω + J ω) ^ 2 ∂P) := by
      apply integral_congr_ae
      filter_upwards [] with ω
      dsimp [J]
      congr 1
      ring
    _ = (t : ℝ) * X.σ ^ 2 +
          (t : ℝ) * (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν) :=
      avram_ja20_integral_square_sum_uncorrelated
        P (R t) J _ _ hG.1 hJ.1 hGJ hCross hG.2 hJ.2
