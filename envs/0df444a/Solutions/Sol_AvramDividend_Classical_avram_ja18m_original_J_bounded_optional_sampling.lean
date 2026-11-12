-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18m_original_J_bounded_optional_sampling
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:40:44.597517+00:00
-- url     : https://prove2.me/submissions/3b0bebbd-6ec2-4c2f-bd5c-ea40ab1f3e59

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_ja18p_original_J_rightcont_integrable_envelope
import Theorems.Thm_AvramDividend_Classical_avram_j18_original_bounded_band_rightcont_optional_sampling
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original compensated J martingale is stopped by the proved general
right-continuous bounded optional-sampling result, using its physical envelope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hRint : ∀ t : ℝ≥0, Integrable (R t) P)
    (hRmart : ∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont s) P (R t) ω = R s ω)
    (n : ℕ) (hn : 0 < n)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0)) :
    let μ : ℝ := ∫ ω, X.X 1 ω ∂P
    let J : ℝ≥0 → Ω → ℝ :=
      fun t ω => X.X t ω - (t : ℝ) * μ - R t ω
    (∀ t : ℝ≥0, Integrable (J t) P) →
    (∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont s) P (J t) ω = J s ω) →
    Integrable (fun ω => J (τ ω) ω) P ∧
    (∀ᵐ ω ∂P,
      condExp (𝓕.rightCont 0) P
        (fun ω => J (τ ω) ω) ω = 0) := by
  let μ : ℝ := ∫ ω, X.X 1 ω ∂P
  let J : ℝ≥0 → Ω → ℝ :=
    fun t ω => X.X t ω - (t : ℝ) * μ - R t ω
  change (∀ t : ℝ≥0, Integrable (J t) P) →
    (∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont s) P (J t) ω = J s ω) →
    Integrable (fun ω => J (τ ω) ω) P ∧
    (∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P
      (fun ω => J (τ ω) ω) ω = 0)
  intro hJint hJmart
  obtain ⟨B, hBInt, hRight, hZero, hDom⟩ :=
    avram_ja18p_original_J_rightcont_integrable_envelope
      X hX hFinite R hRsource hRint hRmart n hn
  exact avram_j18_original_bounded_band_rightcont_optional_sampling
    X hX hFinite n hn τ hτstop hτbound
    J B hJint hJmart hRight hZero hBInt hDom
