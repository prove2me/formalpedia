-- Prove2me | solution 1 for AvramDividend.Classical.avram_b40_original_finite_range_intrinsic_centered_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:48:53.603813+00:00
-- url     : https://prove2.me/submissions/a519b00d-c342-45c4-8a13-fc3e313c61f4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b32_original_finite_range_two_intrinsic_centered_sources_exist
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine finite-range stopped mixed intrinsic source is initially centred. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (S : Finset ℝ≥0) (hτrange : ∀ ω, τ ω ∈ S)
    (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A) :
    ∃ (R Jsmall : ℝ≥0 → Ω → ℝ) (M : Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, Tendsto
        (fun k : ℕ => avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (R t ω))) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, Tendsto
        (fun k : ℕ => avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (𝓝 (Jsmall t ω))) ∧
      Integrable M P ∧
      (∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P M ω = 0) ∧
      (∀ ω, M ω = R (τ ω) ω + Jsmall (τ ω) ω) ∧
      (∫ ω in A, M ω ∂P) = 0 := by 
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨R, Jsmall, MG, MJ, hRs, hJs, hRI, hRM,
    hJI, hJM, hMGI, hMJI, hMG0, hMJ0, hMGsrc, hMJsrc⟩ :=
    avram_b32_original_finite_range_two_intrinsic_centered_sources_exist
      X hX hFinite n hn τ hτstop hτbound S hτrange
  let M : Ω → ℝ := MG + MJ
  have hMI : Integrable M P := hMGI.add hMJI
  have hM0 : ∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P M ω = 0 := by
    filter_upwards [condExp_add hMGI hMJI (𝓕.rightCont 0),
      hMG0, hMJ0] with ω hSum hG hJ
    dsimp [M] at hSum ⊢
    rw [hSum]
    simp [hG, hJ]
  have hSource (ω : Ω) : M ω = R (τ ω) ω + Jsmall (τ ω) ω := by
    simp only [M, Pi.add_apply, hMGsrc ω, hMJsrc ω]
  have hMean : (∫ ω in A, M ω ∂P) = 0 := by
    have hEq := setIntegral_condExp ((𝓕.rightCont).le 0) hMI hA
    rw [← hEq]
    exact integral_eq_zero_of_ae (ae_restrict_of_ae hM0)
  exact ⟨R, Jsmall, M, hRs, hJs, hMI, hM0, hSource, hMean⟩
