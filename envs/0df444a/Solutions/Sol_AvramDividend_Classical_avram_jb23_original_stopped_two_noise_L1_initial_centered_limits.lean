-- Prove2me | solution 1 for AvramDividend.Classical.avram_jb23_original_stopped_two_noise_L1_initial_centered_limits
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:12:56.820196+00:00
-- url     : https://prove2.me/submissions/a17a9158-37a1-4b25-82cd-eb5d06cf4cf0

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jb21_original_two_channel_masked_initial_condexp
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_dominated_condExp_zero_limit
import Theorems.Thm_AvramDividend_Classical_avram_jb22_original_stopped_two_noise_dominated_mesh_limit
import Theorems.Thm_AvramDividend_Classical_avram_jb23_dominated_two_channel_initial_centering_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original stopped predictable Gaussian and jump noise limits are L1 and initially centred. -/
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
    (hJdom : ∀ k, ∀ᵐ ω ∂P, ‖Jseq k ω‖ ≤ BJ ω) :
    Integrable MG P ∧
    (P[MG | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ))) ∧
    Integrable MJ P ∧
    (P[MJ | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ))) := by
  have hCell (k : ℕ) :=
    avram_jb21_original_two_channel_masked_initial_condexp
      (S k) R J hRint hRmart hJint hJmart
      (a k) (b k) (WG k) (WJ k)
      (hab k) (hWG k) (hWJ k) τ hτ
      (hGprod k) (hJprod k)
  have hAll (k : ℕ) :
      Integrable (Gseq k) P ∧
      P[Gseq k | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ)) ∧
      Integrable (Jseq k) P ∧
      P[Jseq k | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ)) := by
    have hGeq : Gseq k = (fun ω =>
        ∑ i ∈ S k, (if τ ω ≤ a k i then 0 else WG k i ω) *
          (R (b k i) ω - R (a k i) ω)) := funext (hGsource k)
    have hJeq : Jseq k = (fun ω =>
        ∑ i ∈ S k, (if τ ω ≤ a k i then 0 else WJ k i ω) *
          (J (b k i) ω - J (a k i) ω)) := funext (hJsource k)
    rw [hGeq, hJeq]
    exact hCell k
  exact avram_jb23_dominated_two_channel_initial_centering_L1
    Gseq Jseq MG MJ BG BJ
    (fun k => (hAll k).1) (fun k => (hAll k).2.2.1)
    hGconv hJconv hBG hBJ hGdom hJdom
    (fun k => (hAll k).2.1) (fun k => (hAll k).2.2.2)
