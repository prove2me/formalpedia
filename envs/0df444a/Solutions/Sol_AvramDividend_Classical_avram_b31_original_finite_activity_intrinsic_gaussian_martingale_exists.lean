-- Prove2me | solution 1 for AvramDividend.Classical.avram_b31_original_finite_activity_intrinsic_gaussian_martingale_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:12:33.295304+00:00
-- url     : https://prove2.me/submissions/415e5877-89ba-47de-8817-5124c9547816

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_limit_rightCont_ae_adapted
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin16_gaussian_residual_original_martingale_l1_public
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The genuine original finite-activity Gaussian residual exists as a same-filtration L1 martingale. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∃ R : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P,
        (∀ T : ℝ≥0,
          Tendsto
            (fun n : ℕ =>
              avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω)
            atTop (𝓝 (R T ω))) ∧
        (∀ K : ℕ, ∀ η : ℝ, 0 < η →
          ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
            ∀ T : ℝ≥0, T ≤ (K : ℝ≥0) →
            |avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω -
              R T ω| ≤ η)) ∧
      (∀ T : ℝ≥0,
        AEStronglyMeasurable[𝓕.rightCont T] (R T) P) ∧
      (∀ T : ℝ≥0, Integrable (R T) P) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        ∀ᵐ ω ∂P,
          condExp (𝓕.rightCont s) P (R t) ω = R s ω) := by
  obtain ⟨R, hLimit, hAdapt⟩ :=
    avram_mix_gauss14_original_intrinsic_limit_rightCont_ae_adapted
      X hFinite
  have hRsource : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω)
          atTop (𝓝 (R T ω)) := by
    filter_upwards [hLimit] with ω hω
    exact hω.1
  obtain ⟨hInt, hMart⟩ :=
    avram_mix_fin16_gaussian_residual_original_martingale_l1_public
      X hX hFinite R hRsource hAdapt
  exact ⟨R, hLimit, hAdapt, hInt, hMart⟩
