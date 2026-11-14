-- Prove2me | solution 3 for AvramDividend.Classical.avram_mix_fin17_original_same_space_gaussian_martingale_bracket_public
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:31:21.749535+00:00
-- url     : https://prove2.me/submissions/cd9f8aee-6ac6-495e-ba2c-57a17e4e7977
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_limit_rightCont_ae_adapted
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin16_gaussian_residual_original_martingale_l1_public
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin16_gaussian_residual_original_bracket_l2_public
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Assemble the original-filtration Gaussian martingale and its exact bracket from proved source construction and second-moment bridge. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∃ R : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
          atTop (nhds (R t ω))) ∧
      (∀ t : ℝ≥0,
        AEStronglyMeasurable[𝓕.rightCont t] (R t) P) ∧
      (∀ t : ℝ≥0, Integrable (R t) P) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        ∀ᵐ ω ∂P,
          condExp (𝓕.rightCont s) P (R t) ω = R s ω) ∧
      (∀ t : ℝ≥0,
        Integrable (fun ω => (R t ω) ^ 2) P ∧
        (∫ ω, (R t ω) ^ 2 ∂P) = (t : ℝ) * X.σ ^ 2) := by
  obtain ⟨R, hLimit, hAdapt⟩ :=
    avram_mix_gauss14_original_intrinsic_limit_rightCont_ae_adapted
      X hFinite
  have hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)) := by
    filter_upwards [hLimit] with ω hω
    exact hω.1
  obtain ⟨hInt, hMart⟩ :=
    avram_mix_fin16_gaussian_residual_original_martingale_l1_public
      X hX hFinite R hRsource hAdapt
  have hSquare :=
    avram_mix_fin16_gaussian_residual_original_bracket_l2_public
      X hX hFinite R hRsource hAdapt
  exact ⟨R, hRsource, hAdapt, hInt, hMart, hSquare⟩
