-- Prove2me | solution 1 for AvramDividend.Classical.avram_b41_original_finite_range_two_source_L1_stop_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:55:17.98653+00:00
-- url     : https://prove2.me/submissions/30f42e60-8888-4c19-8592-e89789046041

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b40_original_finite_range_intrinsic_centered_sum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine finite-range intrinsic mixed noise stays centred at every restricted L1 limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (hn : 0 < n) (τ : ℕ → Ω → ℝ≥0)
    (hτstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (τ k ω : WithTop ℝ≥0)))
    (hτbound : ∀ k ω, τ k ω ≤ (n : ℝ≥0))
    (S : ℕ → Finset ℝ≥0) (hτrange : ∀ k ω, τ k ω ∈ S k)
    (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A) :
    ∃ (R Jsmall : ℕ → ℝ≥0 → Ω → ℝ) (M : ℕ → Ω → ℝ),
      (∀ k, Integrable (M k) P ∧
        (∫ ω in A, M k ω ∂P) = 0 ∧
        (∀ ω, M k ω = R k (τ k ω) ω + Jsmall k (τ k ω) ω)) ∧
      ∀ (Z : Ω → ℝ), Integrable Z P →
        Tendsto (fun k => ∫⁻ ω in A,
          ‖M k ω - Z ω‖ₑ ∂P) atTop (𝓝 (0 : ℝ≥0∞)) →
        (∫ ω in A, Z ω ∂P) = 0 := by 
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  have hStep (k : ℕ) :
      ∃ (R Jsmall : ℝ≥0 → Ω → ℝ) (Mk : Ω → ℝ),
        Integrable Mk P ∧
        (∫ ω in A, Mk ω ∂P) = 0 ∧
        (∀ ω, Mk ω = R (τ k ω) ω + Jsmall (τ k ω) ω) := by
    obtain ⟨R, J, Mk, _, _, hMI, _, hSrc, hZero⟩ :=
      avram_b40_original_finite_range_intrinsic_centered_sum
        X hX hFinite n hn (τ k) (hτstop k) (hτbound k)
        (S k) (hτrange k) A hA
    exact ⟨R, J, Mk, hMI, hZero, hSrc⟩
  choose R Jsmall M hMI hZero hSource using hStep
  refine ⟨R, Jsmall, M, ?_, ?_⟩
  · exact fun k => ⟨hMI k, hZero k, hSource k⟩
  intro Z hZI hL1
  have hT :=
    tendsto_integral_of_L1 Z hZI.integrableOn.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun k => (hMI k).integrableOn)) hL1
  have hZeroFn :
      (fun k : ℕ => ∫ ω in A, M k ω ∂P) =
      (fun _ : ℕ => (0 : ℝ)) := by
    funext k
    exact hZero k
  rw [hZeroFn] at hT
  exact (tendsto_nhds_unique tendsto_const_nhds hT).symm
