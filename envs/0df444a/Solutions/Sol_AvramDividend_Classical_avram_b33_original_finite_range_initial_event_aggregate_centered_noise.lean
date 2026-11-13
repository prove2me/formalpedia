-- Prove2me | solution 1 for AvramDividend.Classical.avram_b33_original_finite_range_initial_event_aggregate_centered_noise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:23:07.763594+00:00
-- url     : https://prove2.me/submissions/0ea5b745-717a-4368-9aa8-cc164c80d4fa

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b32_original_finite_range_two_intrinsic_centered_sources_exist
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_past_event_integral_of_condexp_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original physical finite-range mixed stopped aggregate noise is centred on every initial-filtration event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (hn : 0 < n)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (S : Finset ℝ≥0) (hτrange : ∀ ω, τ ω ∈ S) :
    ∃ (M : Ω → ℝ) (R Jsmall : ℝ≥0 → Ω → ℝ),
      Integrable M P ∧
      (∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A →
        (∫ ω in A, M ω ∂P) = 0) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto
          (fun k : ℕ =>
            avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
          atTop (𝓝 (R t ω))) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto
          (fun k : ℕ =>
            avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
          atTop (𝓝 (Jsmall t ω))) ∧
      (∀ ω, M ω = R (τ ω) ω + Jsmall (τ ω) ω) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨R, Jsmall, MG, MJ, hRsource, hJsource,
      hRint, hRmart, hJint, hJmart, hMGint, hMJint,
      hMGzero, hMJzero, hMGsource, hMJsource⟩ :=
    avram_b32_original_finite_range_two_intrinsic_centered_sources_exist
      X hX hFinite n hn τ hτstop hτbound S hτrange
  refine ⟨MG + MJ, R, Jsmall, hMGint.add hMJint, ?_,
    hRsource, hJsource, ?_⟩
  · intro A hA
    have hMGA : (∫ ω in A, MG ω ∂P) = 0 :=
      avram_ubv_jump11_past_event_integral_of_condexp_zero
        (𝓕.rightCont 0) (𝓕.rightCont.le 0)
        MG hMGint hMGzero A hA
    have hMJA : (∫ ω in A, MJ ω ∂P) = 0 :=
      avram_ubv_jump11_past_event_integral_of_condexp_zero
        (𝓕.rightCont 0) (𝓕.rightCont.le 0)
        MJ hMJint hMJzero A hA
    change (∫ ω in A, MG ω + MJ ω ∂P) = 0
    rw [integral_add hMGint.integrableOn hMJint.integrableOn,
      hMGA, hMJA]
    norm_num
  · intro ω
    simp only [Pi.add_apply, hMGsource ω, hMJsource ω]
