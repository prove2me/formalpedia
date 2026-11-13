-- Prove2me | solution 3 for AvramDividend.Classical.avram_mix_fin16_gaussian_residual_original_bracket_l2_public
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T23:48:06.932303+00:00
-- url     : https://prove2.me/submissions/def70f2e-1f12-4095-a948-928e241dd128
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_anoise22_original_gaussian_cutoff_exact_second_moment
import Theorems.Thm_AvramDividend_Classical_avram_anoise23_original_residual_square_integrable_of_cutoff
import Theorems.Thm_AvramDividend_Classical_avram_anoise24_original_cutoff_square_expectations_converge
import Theorems.Thm_AvramDividend_Classical_avram_ja22_original_finite_activity_real_levy_tail_square_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Exact original Gaussian limit L2 bracket from its physical cutoff
variance and the true near-zero source Lévy squared-mass convergence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hRadapt : ∀ t : ℝ≥0,
      AEStronglyMeasurable[𝓕.rightCont t] (R t) P) :
    ∀ t : ℝ≥0,
      Integrable (fun ω => (R t ω) ^ 2) P ∧
      (∫ ω, (R t ω) ^ 2 ∂P) = (t : ℝ) * X.σ ^ 2 := by
  intro t
  have hSrc : ∀ᵐ ω ∂P, Tendsto (fun k : ℕ =>
      avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
      atTop (nhds (R t ω)) := by
    filter_upwards [hRsource] with ω hω
    exact hω t
  have hMeas : ∀ k : ℕ, AEStronglyMeasurable
      (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω) P :=
    fun k => ((avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
      X k t).mono (𝓕.le t) le_rfl).aestronglyMeasurable
  have hRmeas : AEStronglyMeasurable (R t) P :=
    aestronglyMeasurable_of_tendsto_ae atTop hMeas hSrc
  have hCut := fun n => avram_anoise22_original_gaussian_cutoff_exact_second_moment
    X hX hFinite n t
  have hInt : Integrable (fun ω => (R t ω) ^ 2) P :=
    avram_anoise23_original_residual_square_integrable_of_cutoff
      X hFinite R t hSrc hRmeas hMeas (hCut 0).1
  have hLimit := avram_anoise24_original_cutoff_square_expectations_converge
    X hFinite R t hSrc hMeas (hCut 0).1
  have hTail := avram_ja22_original_finite_activity_real_levy_tail_square_tendsto_zero
    X hFinite
  have hTailScaled : Tendsto (fun n : ℕ => (t : ℝ) *
      (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν))
      atTop (nhds (0 : ℝ)) := by
    simpa using (tendsto_const_nhds.mul hTail :
      Tendsto (fun n : ℕ => (t : ℝ) *
        (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν))
      atTop (nhds ((t : ℝ) * 0)))
  have hTarget : Tendsto (fun n : ℕ =>
      (t : ℝ) * X.σ ^ 2 +
      (t : ℝ) * (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0,
        z ^ 2 ∂X.ν))
      atTop (nhds ((t : ℝ) * X.σ ^ 2)) := by
    simpa using (tendsto_const_nhds.add hTailScaled)
  have hCutEq : (fun n : ℕ => ∫ ω,
      (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) ^ 2 ∂P) =
      (fun n : ℕ => (t : ℝ) * X.σ ^ 2 +
        (t : ℝ) * (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0,
          z ^ 2 ∂X.ν)) := by
    funext n
    exact (hCut n).2
  rw [hCutEq] at hLimit
  exact ⟨hInt, tendsto_nhds_unique hLimit hTarget⟩
