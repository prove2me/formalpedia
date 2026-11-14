-- Prove2me | solution 1 for AvramDividend.Classical.avram_b48_original_predictably_weighted_intrinsic_L1_event_centered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:05:10.120363+00:00
-- url     : https://prove2.me/submissions/4d4be7de-f54e-4781-82a9-06b0b5a872f9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b32_original_finite_range_two_intrinsic_centered_sources_exist
import Theorems.Thm_AvramDividend_Classical_avram_jb23_original_stopped_two_noise_L1_initial_centered_limits
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine predictable weighted original intrinsic Gaussian and jump L1 gains are initially centred. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hStop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hBound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (T : Finset ℝ≥0) (hRange : ∀ ω, τ ω ∈ T)
    (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A) :
    ∃ (R J : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
          atTop (𝓝 (R t ω))) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
          atTop (𝓝 (J t ω))) ∧
      ∀ {ι : Type*} (S : ℕ → Finset ι)
        (a b : ℕ → ι → ℝ≥0)
        (WG WJ : ℕ → ι → Ω → ℝ),
        (∀ k, ∀ i ∈ S k, a k i ≤ b k i) →
        (∀ k, ∀ i ∈ S k, Measurable[𝓕.rightCont (a k i)] (WG k i)) →
        (∀ k, ∀ i ∈ S k, Measurable[𝓕.rightCont (a k i)] (WJ k i)) →
        (∀ k, ∀ i ∈ S k, Integrable (fun ω =>
          (if τ ω ≤ a k i then 0 else WG k i ω) *
            (R (b k i) ω - R (a k i) ω)) P) →
        (∀ k, ∀ i ∈ S k, Integrable (fun ω =>
          (if τ ω ≤ a k i then 0 else WJ k i ω) *
            (J (b k i) ω - J (a k i) ω)) P) →
        ∀ (Gseq Jseq : ℕ → Ω → ℝ),
        (∀ k ω, Gseq k ω =
          ∑ i ∈ S k, (if τ ω ≤ a k i then 0 else WG k i ω) *
            (R (b k i) ω - R (a k i) ω)) →
        (∀ k ω, Jseq k ω =
          ∑ i ∈ S k, (if τ ω ≤ a k i then 0 else WJ k i ω) *
            (J (b k i) ω - J (a k i) ω)) →
        ∀ (MG MJ BG BJ : Ω → ℝ),
        (∀ᵐ ω ∂P, Tendsto (fun k => Gseq k ω) atTop (𝓝 (MG ω))) →
        (∀ᵐ ω ∂P, Tendsto (fun k => Jseq k ω) atTop (𝓝 (MJ ω))) →
        Integrable BG P → Integrable BJ P →
        (∀ k, ∀ᵐ ω ∂P, ‖Gseq k ω‖ ≤ BG ω) →
        (∀ k, ∀ᵐ ω ∂P, ‖Jseq k ω‖ ≤ BJ ω) →
        Integrable (fun ω => MG ω + MJ ω) P ∧
        (∫ ω in A, MG ω + MJ ω ∂P) = 0 := by 
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨R, J, _, _, hRs, hJs, hRI, hRM,
      hJI, hJM, _, _, _, _, _, _⟩ :=
    avram_b32_original_finite_range_two_intrinsic_centered_sources_exist
      X hX hFinite n hn τ hStop hBound T hRange
  refine ⟨R, J, hRs, hJs, ?_⟩
  intro ι S a b WG WJ hab hWG hWJ hGp hJp
    Gseq Jseq hGs hJs2 MG MJ BG BJ hGc hJc
    hBG hBJ hGdom hJdom
  obtain ⟨hMGI, hMG0, hMJI, hMJ0⟩ :=
    avram_jb23_original_stopped_two_noise_L1_initial_centered_limits
      S R J hRI hRM hJI hJM a b WG WJ hab hWG hWJ
      τ hStop hGp hJp Gseq Jseq hGs hJs2 MG MJ BG BJ
      hGc hJc hBG hBJ hGdom hJdom
  have hSumI : Integrable (fun ω => MG ω + MJ ω) P :=
    hMGI.add hMJI
  have hSum0fun : ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont 0) P (MG + MJ) ω = 0 := by
    filter_upwards [condExp_add hMGI hMJI (𝓕.rightCont 0),
      hMG0, hMJ0] with ω hadd hG hJ
    calc
      condExp (𝓕.rightCont 0) P (MG + MJ) ω =
          condExp (𝓕.rightCont 0) P MG ω +
          condExp (𝓕.rightCont 0) P MJ ω := hadd
      _ = 0 := by rw [hG, hJ]; ring
  have hSame : (MG + MJ) = (fun η => MG η + MJ η) := by
    funext η
    rfl
  have hSum0 : ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont 0) P
        (fun η => MG η + MJ η) ω = 0 := by
    rw [← hSame]
    exact hSum0fun
  have hMean : (∫ ω in A, MG ω + MJ ω ∂P) = 0 := by
    have hh : (∫ ω in A, MG ω + MJ ω ∂P) =
        (∫ ω in A, condExp (𝓕.rightCont 0) P
          (fun η => MG η + MJ η) ω ∂P) :=
      (setIntegral_condExp ((𝓕.rightCont).le 0) hSumI hA).symm
    exact hh.trans (integral_eq_zero_of_ae (ae_restrict_of_ae hSum0))
  exact ⟨hSumI, hMean⟩
