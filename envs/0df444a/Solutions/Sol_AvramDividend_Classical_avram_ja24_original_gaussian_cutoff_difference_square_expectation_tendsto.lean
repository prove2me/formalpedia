-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja24_original_gaussian_cutoff_difference_square_expectation_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T17:37:30.227969+00:00
-- url     : https://prove2.me/submissions/cdaffd92-0aac-4879-8134-7f305f9a7ccb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
import Theorems.Thm_AvramDividend_Classical_avram_anoise21_original_gaussian_residual_L2_cutoff_error
import Theorems.Thm_AvramDividend_Classical_avram_ja25_original_gaussian_difference_integrable_dominator
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Transfer the original finite-count envelope through square dominated convergence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
        atTop (nhds (R T ω)))
    (hStrip : ∀ (n m : ℕ), n ≤ m → ∀ (t : ℝ≥0),
      Integrable (fun ω =>
        (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω -
          avram_p4_h_gaussian_intrinsic_truncated_residual X m t ω) ^ 2) P ∧
      (∫ ω, (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω -
          avram_p4_h_gaussian_intrinsic_truncated_residual X m t ω) ^ 2 ∂P) =
        (t : ℝ) * (∫ z in Ioc
          (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1))), z ^ 2 ∂X.ν)) :
    ∀ n : ℕ, ∀ t : ℝ≥0,
      Integrable (fun ω =>
        (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω - R t ω) ^ 2) P ∧
      Tendsto
        (fun m : ℕ => ∫ ω,
          (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω -
            avram_p4_h_gaussian_intrinsic_truncated_residual X m t ω) ^ 2 ∂P)
        atTop (nhds (∫ ω,
          (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω -
            R t ω) ^ 2 ∂P)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro n t
  let F : ℕ → Ω → ℝ := fun k ω =>
    avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω
  have hSource : ∀ᵐ ω ∂P, Tendsto (fun k => F k ω) atTop (nhds (R t ω)) := by
    filter_upwards [hR] with ω hω
    exact hω t
  have hCutMeas (k : ℕ) : AEStronglyMeasurable (F k) P := by
    have hm : Measurable (F k) :=
      (avram_mix_gauss14_original_intrinsic_truncated_residual_adapted X k t).mono
        (𝓕.le t) le_rfl
    exact hm.aestronglyMeasurable
  have hRmeas : AEStronglyMeasurable (R t) P :=
    aestronglyMeasurable_of_tendsto_ae atTop hCutMeas hSource
  have hInt0 := (avram_anoise21_original_gaussian_residual_L2_cutoff_error
    X hFinite R t hSource hRmeas hCutMeas n).1
  have hInt : Integrable (fun ω => (F n ω - R t ω) ^ 2) P := by
    have heq : (fun ω => (F n ω - R t ω) ^ 2) =
        (fun ω => (R t ω - F n ω) ^ 2) := by
      funext ω
      ring
    rw [heq]
    exact hInt0
  obtain ⟨G, hG, hBound⟩ :=
    avram_ja25_original_gaussian_difference_integrable_dominator X hFinite R hR n t
  let f : ℕ → Ω → ℝ := fun k ω => (F n ω - F k ω) ^ 2
  have hf (k : ℕ) : AEStronglyMeasurable (f k) P :=
    ((hCutMeas n).sub (hCutMeas k)).pow 2
  have hLim : ∀ᵐ ω ∂P,
      Tendsto (fun k => f k ω) atTop (nhds ((F n ω - R t ω) ^ 2)) := by
    filter_upwards [hSource] with ω hω
    exact (tendsto_const_nhds.sub hω).pow 2
  have hDCT : Tendsto (fun k => ∫ ω, f k ω ∂P)
      atTop (nhds (∫ ω, (F n ω - R t ω) ^ 2 ∂P)) :=
    tendsto_integral_of_dominated_convergence G hf hG (by simpa only [f, F] using hBound) hLim
  exact ⟨hInt, by simpa only [f, F] using hDCT⟩