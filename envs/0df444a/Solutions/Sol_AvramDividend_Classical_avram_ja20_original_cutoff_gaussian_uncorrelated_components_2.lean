-- Prove2me | solution 2 for AvramDividend.Classical.avram_ja20_original_cutoff_gaussian_uncorrelated_components
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:00:45.989588+00:00
-- url     : https://prove2.me/submissions/c9a037b9-6f14-497d-94af-14b1bd6c68b5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin13_original_finite_activity_intrinsic_residual_uniform_limit_field_ae
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
import Theorems.Thm_AvramDividend_Classical_avram_ja20_integrable_product_of_square_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ja22_original_limit_gaussian_exact_square_moment
import Theorems.Thm_AvramDividend_Classical_avram_ja22_original_omitted_nearzero_tail_exact_square_moment
import Theorems.Thm_AvramDividend_Classical_avram_ja22_original_limit_gaussian_omitted_tail_zero_cross
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
        Integrable (fun ω => (G ω) ^ 2) P ∧
        Integrable (fun ω => (J ω) ^ 2) P ∧
        Integrable (fun ω => G ω * J ω) P ∧
        (∫ ω, G ω * J ω ∂P) = 0 ∧
        (∫ ω, (G ω) ^ 2 ∂P) = (t : ℝ) * X.σ ^ 2 ∧
        (∫ ω, (J ω) ^ 2 ∂P) =
          (t : ℝ) * (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν) := by
  obtain ⟨R, hR0⟩ :=
    avram_mix_fin13_original_finite_activity_intrinsic_residual_uniform_limit_field_ae X hFinite
  have hR : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
        atTop (nhds (R T ω)) := by
    filter_upwards [hR0] with ω hω
    exact hω.1
  intro n t
  let G : Ω → ℝ := fun ω => R t ω
  let J : Ω → ℝ := fun ω =>
    avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω - R t ω
  have hf : ∀ k : ℕ,
      AEStronglyMeasurable (fun ω =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω) P := by
    intro k
    exact ((avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
      X k t).mono (𝓕.le t) le_rfl).aestronglyMeasurable
  have hRt : ∀ᵐ ω ∂P,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)) := by
    filter_upwards [hR] with ω hω
    exact hω t
  have hGMeas : AEStronglyMeasurable G P := by
    exact aestronglyMeasurable_of_tendsto_ae atTop hf hRt
  have hJMeas : AEStronglyMeasurable J P := by
    exact (hf n).sub hGMeas
  obtain ⟨hGsq, hGmom⟩ :=
    avram_ja22_original_limit_gaussian_exact_square_moment X hX hFinite R hR t
  obtain ⟨hJsq, hJmom⟩ :=
    avram_ja22_original_omitted_nearzero_tail_exact_square_moment X hX hFinite R hR n t
  have hCross :=
    avram_ja22_original_limit_gaussian_omitted_tail_zero_cross X hX hFinite R hR n t
  refine ⟨G, J, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [] with ω
    dsimp [G, J]
    ring
  · simpa only [G] using hGsq
  · simpa only [J] using hJsq
  · exact avram_ja20_integrable_product_of_square_integrable
      P G J hGMeas hJMeas (by simpa only [G] using hGsq)
      (by simpa only [J] using hJsq)
  · simpa only [G, J] using hCross
  · simpa only [G] using hGmom
  · simpa only [J] using hJmom
