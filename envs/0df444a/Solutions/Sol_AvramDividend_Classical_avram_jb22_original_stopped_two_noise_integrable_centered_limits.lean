-- Prove2me | solution 1 for AvramDividend.Classical.avram_jb22_original_stopped_two_noise_integrable_centered_limits
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:40:21.488562+00:00
-- url     : https://prove2.me/submissions/98e60ee6-7129-4685-90d2-9ae5eefaead2

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jb22_original_stopped_two_noise_dominated_mesh_limit
import Theorems.Thm_avram_jb22_original_stopped_two_noise_integrable_cen_pointwise_upper_bound_abe809fc
import Theorems.Thm_avram_jb22_original_stopped_two_noise_integrable_cen_pointwise_upper_bound_f660f5d4
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original dominated stopped two-noise limits are integrable and initially centred. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {ι : Type*} (S : ℕ → Finset ι)
    (R J : ℝ≥0 → Ω → ℝ)
    (hRint : ∀ u : ℝ≥0, Integrable (R u) P)
    (hRmart : ∀ u v : ℝ≥0, u ≤ v →
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont u) P (R v) ω = R u ω)
    (hJint : ∀ u : ℝ≥0, Integrable (J u) P)
    (hJmart : ∀ u v : ℝ≥0, u ≤ v →
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont u) P (J v) ω = J u ω)
    (a b : ℕ → ι → ℝ≥0)
    (WG WJ : ℕ → ι → Ω → ℝ)
    (hab : ∀ k, ∀ i ∈ S k, a k i ≤ b k i)
    (hWG : ∀ k, ∀ i ∈ S k,
      Measurable[𝓕.rightCont (a k i)] (WG k i))
    (hWJ : ∀ k, ∀ i ∈ S k,
      Measurable[𝓕.rightCont (a k i)] (WJ k i))
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hGprod : ∀ k, ∀ i ∈ S k,
      Integrable (fun ω =>
        (if τ ω ≤ a k i then 0 else WG k i ω) *
          (R (b k i) ω - R (a k i) ω)) P)
    (hJprod : ∀ k, ∀ i ∈ S k,
      Integrable (fun ω =>
        (if τ ω ≤ a k i then 0 else WJ k i ω) *
          (J (b k i) ω - J (a k i) ω)) P)
    (Gseq Jseq : ℕ → Ω → ℝ)
    (hGsource : ∀ k ω, Gseq k ω =
      ∑ i ∈ S k, (if τ ω ≤ a k i then 0 else WG k i ω) *
        (R (b k i) ω - R (a k i) ω))
    (hJsource : ∀ k ω, Jseq k ω =
      ∑ i ∈ S k, (if τ ω ≤ a k i then 0 else WJ k i ω) *
        (J (b k i) ω - J (a k i) ω))
    (MG MJ BG BJ : Ω → ℝ)
    (hGconv : ∀ᵐ ω ∂P,
      Tendsto (fun k => Gseq k ω) atTop (𝓝 (MG ω)))
    (hJconv : ∀ᵐ ω ∂P,
      Tendsto (fun k => Jseq k ω) atTop (𝓝 (MJ ω)))
    (hBG : Integrable BG P) (hBJ : Integrable BJ P)
    (hGdom : ∀ k, ∀ᵐ ω ∂P, ‖Gseq k ω‖ ≤ BG ω)
    (hJdom : ∀ k, ∀ᵐ ω ∂P, ‖Jseq k ω‖ ≤ BJ ω)
    (hMGAE : AEStronglyMeasurable MG P)
    (hMJAE : AEStronglyMeasurable MJ P) :
    Integrable MG P ∧
    (P[MG | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ))) ∧
    Integrable MJ P ∧
    (P[MJ | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ))) := by
  have hGdomall : ∀ᵐ ω ∂P, ∀ k, ‖Gseq k ω‖ ≤ BG ω :=
    ae_all_iff.mpr hGdom
  have hJdomall : ∀ᵐ ω ∂P, ∀ k, ‖Jseq k ω‖ ≤ BJ ω :=
    ae_all_iff.mpr hJdom
  have hGbound : ∀ᵐ ω ∂P, ‖MG ω‖ ≤ ‖BG ω‖ := avram_jb22_original_stopped_two_noise_integrable_cen_pointwise_upper_bound_abe809fc (Ω := Ω) (mΩ := mΩ) (P := P) (𝓕 := 𝓕) (ι := ι) (S := S) (R := R) (J := J) (hRint := hRint) (hRmart := hRmart) (hJint := hJint) (hJmart := hJmart) (a := a) (b := b) (WG := WG) (WJ := WJ) (hab := hab) (hWG := hWG) (hWJ := hWJ) (τ := τ) (hτ := hτ) (hGprod := hGprod) (hJprod := hJprod) (Gseq := Gseq) (Jseq := Jseq) (hGsource := hGsource) (hJsource := hJsource) (MG := MG) (MJ := MJ) (BG := BG) (BJ := BJ) (hGconv := hGconv) (hJconv := hJconv) (hBG := hBG) (hBJ := hBJ) (hGdom := hGdom) (hJdom := hJdom) (hMGAE := hMGAE) (hMJAE := hMJAE) (hGdomall := hGdomall) (hJdomall := hJdomall)
  have hJbound : ∀ᵐ ω ∂P, ‖MJ ω‖ ≤ ‖BJ ω‖ := avram_jb22_original_stopped_two_noise_integrable_cen_pointwise_upper_bound_f660f5d4 (Ω := Ω) (mΩ := mΩ) (P := P) (𝓕 := 𝓕) (ι := ι) (S := S) (R := R) (J := J) (hRint := hRint) (hRmart := hRmart) (hJint := hJint) (hJmart := hJmart) (a := a) (b := b) (WG := WG) (WJ := WJ) (hab := hab) (hWG := hWG) (hWJ := hWJ) (τ := τ) (hτ := hτ) (hGprod := hGprod) (hJprod := hJprod) (Gseq := Gseq) (Jseq := Jseq) (hGsource := hGsource) (hJsource := hJsource) (MG := MG) (MJ := MJ) (BG := BG) (BJ := BJ) (hGconv := hGconv) (hJconv := hJconv) (hBG := hBG) (hBJ := hBJ) (hGdom := hGdom) (hJdom := hJdom) (hMGAE := hMGAE) (hMJAE := hMJAE) (hGdomall := hGdomall) (hJdomall := hJdomall) (hGbound := hGbound)
  have hGI : Integrable MG P := hBG.mono hMGAE hGbound
  have hJI : Integrable MJ P := hBJ.mono hMJAE hJbound
  have hZ :=
    avram_jb22_original_stopped_two_noise_dominated_mesh_limit
      S R J hRint hRmart hJint hJmart
      a b WG WJ hab hWG hWJ τ hτ
      hGprod hJprod Gseq Jseq hGsource hJsource
      MG MJ BG BJ hGconv hJconv hBG hBJ hGdom hJdom
  exact ⟨hGI, hZ.1, hJI, hZ.2⟩
