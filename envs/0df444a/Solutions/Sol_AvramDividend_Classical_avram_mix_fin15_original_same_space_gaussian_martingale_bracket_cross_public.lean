-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin15_original_same_space_gaussian_martingale_bracket_cross_public
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T13:09:19.733112+00:00
-- url     : https://prove2.me/submissions/1c4097d9-f275-4677-b062-0abeea2f2c09
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_limit_rightCont_ae_adapted
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin16_gaussian_residual_original_martingale_l1_public
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin16_gaussian_residual_original_bracket_l2_public
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin16_gaussian_residual_original_jump_cross_zero_public
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
    ∃ R : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto
          (fun k : ℕ =>
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
        (∫ ω, (R t ω) ^ 2 ∂P) = (t : ℝ) * X.σ ^ 2) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        let cross : Ω → ℝ := fun ω =>
          (R t ω - R s ω) *
            ((X.X t ω - X.X s ω) - (R t ω - R s ω))
        Integrable cross P ∧ (∫ ω, cross ω ∂P) = 0) := by
  obtain ⟨R, hBoth, hAdapt⟩ :=
    avram_mix_gauss14_original_intrinsic_limit_rightCont_ae_adapted
      X hFinite
  have hSource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)) := by
    filter_upwards [hBoth] with ω hω
    exact hω.1
  obtain ⟨hInt, hMart⟩ :=
    avram_mix_fin16_gaussian_residual_original_martingale_l1_public
      X hX hFinite R hSource hAdapt
  have hBracket :=
    avram_mix_fin16_gaussian_residual_original_bracket_l2_public
      X hX hFinite R hSource hAdapt
  have hCross :=
    avram_mix_fin16_gaussian_residual_original_jump_cross_zero_public
      X hX hFinite R hSource hAdapt
  exact ⟨R, hSource, hAdapt, hInt, hMart, hBracket, hCross⟩
