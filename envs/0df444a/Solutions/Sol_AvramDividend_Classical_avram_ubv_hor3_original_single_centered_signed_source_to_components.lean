-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_hor3_original_single_centered_signed_source_to_components
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T14:33:30.217146+00:00
-- url     : https://prove2.me/submissions/a94d6301-9ded-4abf-ae1c-8b24ee00991a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (τ : Ω → ℝ≥0) (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (M R : Ω → ℝ)
    (hMI : Integrable M P)
    (hZero : (∫ ω, M ω ∂P) = 0)
    (hRnonpos : ∀ᵐ ω ∂P, R ω ≤ 0)
    (hSource : ∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + M ω + R ω) :
    ∃ Mc Ms Ml G R' : Ω → ℝ,
      Integrable Mc P ∧ Integrable Ms P ∧ Integrable Ml P ∧
      Integrable G P ∧
      (∫ ω, Mc ω ∂P) = 0 ∧
      (∫ ω, Ms ω ∂P) = 0 ∧
      (∫ ω, Ml ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω ≤ 0) ∧
      (∀ᵐ ω ∂P, R' ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤
        w x + Mc ω + Ms ω + Ml ω + G ω + R' ω) := by
  refine ⟨M, (fun _ => 0), (fun _ => 0), (fun _ => 0), R,
    hMI, by simp, by simp, by simp,
    hZero, by simp, by simp, by simp, hRnonpos, ?_⟩
  filter_upwards [hSource] with ω hω
  simpa using hω
