-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin15_original_compensated_jump_stopped_martingale_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:26:13.133545+00:00
-- url     : https://prove2.me/submissions/f2b61f99-15f8-4eb5-9474-e31c1698b939

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_ja18l_original_compensated_difference_L1
import Theorems.Thm_AvramDividend_Classical_avram_ja18m_original_J_deterministic_rightcont
import Theorems.Thm_AvramDividend_Classical_avram_ja18m_original_J_bounded_optional_sampling
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original J certificate: separate fixed-time L1, right-continuous
martingale increments, and bounded optional sampling. -/
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
    (∀ t : ℝ≥0, Integrable (J t) P) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        ∀ᵐ ω ∂P,
          condExp (𝓕.rightCont s) P (J t) ω = J s ω) ∧
      Integrable (fun ω => J (τ ω) ω) P ∧
      (∀ᵐ ω ∂P,
        condExp (𝓕.rightCont 0) P
          (fun ω => J (τ ω) ω) ω = 0) := by
  let μ : ℝ := ∫ ω, X.X 1 ω ∂P
  let J : ℝ≥0 → Ω → ℝ :=
    fun t ω => X.X t ω - (t : ℝ) * μ - R t ω
  change (∀ t : ℝ≥0, Integrable (J t) P) ∧
    (∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont s) P (J t) ω = J s ω) ∧
    Integrable (fun ω => J (τ ω) ω) P ∧
    (∀ᵐ ω ∂P,
      condExp (𝓕.rightCont 0) P
        (fun ω => J (τ ω) ω) ω = 0)
  have hJint := avram_ja18l_original_compensated_difference_L1 X hX R hRint
  have hJmart :=
    avram_ja18m_original_J_deterministic_rightcont
      X hX hFinite R hRsource hRint hRmart
  obtain ⟨hStoppedInt, hStoppedMean⟩ :=
    avram_ja18m_original_J_bounded_optional_sampling
      X hX hFinite R hRsource hRint hRmart
      n hn τ hτstop hτbound hJint hJmart
  exact ⟨hJint, hJmart, hStoppedInt, hStoppedMean⟩
