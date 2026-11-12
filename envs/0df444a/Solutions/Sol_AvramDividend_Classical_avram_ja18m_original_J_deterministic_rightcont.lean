-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18m_original_J_deterministic_rightcont
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:26:01.684049+00:00
-- url     : https://prove2.me/submissions/c02f32be-483b-4dc3-9cc5-c78273bd6d56

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_ja18_standing_X_integrable_fixedtime
import Theorems.Thm_AvramDividend_Classical_avram_ja18n_original_X_centered_rightcont_martingale
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Subtract the intrinsic right-continuous martingale R from the
original mean-centred Lévy martingale, on the same filtration and P. -/
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
        condExp (𝓕.rightCont s) P (R t) ω = R s ω) :
    let μ : ℝ := ∫ ω, X.X 1 ω ∂P
    let J : ℝ≥0 → Ω → ℝ :=
      fun t ω => X.X t ω - (t : ℝ) * μ - R t ω
    ∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont s) P (J t) ω = J s ω := by
  letI : IsProbabilityMeasure P := X.isProbability
  let μ : ℝ := ∫ ω, X.X 1 ω ∂P
  let J : ℝ≥0 → Ω → ℝ :=
    fun t ω => X.X t ω - (t : ℝ) * μ - R t ω
  change ∀ s t : ℝ≥0, s ≤ t →
    ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont s) P (J t) ω = J s ω
  intro s t hst
  have hXint : Integrable (X.X t) P :=
    avram_ja18_standing_X_integrable_fixedtime X hX t
  have hCenteredInt :
      Integrable (fun ω => X.X t ω - (t : ℝ) * μ) P :=
    hXint.sub (integrable_const _)
  have hSub := condExp_sub hCenteredInt (hRint t) (𝓕.rightCont s)
  have hXmart :=
    avram_ja18n_original_X_centered_rightcont_martingale
      X hX hFinite s t hst
  filter_upwards [hSub, hXmart, hRmart s t hst] with ω hsub hx hr
  calc
    condExp (𝓕.rightCont s) P (J t) ω =
      condExp (𝓕.rightCont s) P
        (fun ω => X.X t ω - (t : ℝ) * μ) ω -
      condExp (𝓕.rightCont s) P (R t) ω := hsub
    _ = J s ω := by rw [hx, hr]
