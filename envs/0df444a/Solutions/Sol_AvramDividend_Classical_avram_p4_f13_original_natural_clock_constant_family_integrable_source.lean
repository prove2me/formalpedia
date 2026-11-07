-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f13_original_natural_clock_constant_family_integrable_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:54:37.788117+00:00
-- url     : https://prove2.me/submissions/7f7bce55-7343-476c-a3e3-d67c2efaad0d

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermI : Integrable Term P) (hCashI : Integrable Cash P) :
    ∃ (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ),
      (∀ k, IsStoppingTime 𝓕.rightCont (fun ω => (σ k ω : WithTop ℝ≥0))) ∧
      (∀ k ω, σ k ω ≤ τ ω) ∧
      (∀ k ω, F k ω =
        Real.exp (-(q * (σ k ω : ℝ))) *
          w (if σ k ω = 0 ∨ (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) ∧
      (∀ k, Integrable (F k) P) ∧
      (∫ ω, F 0 ω ∂P) = (∫ ω, Term ω + Cash ω ∂P) := by
  refine ⟨(fun _ => τ), (fun _ ω => Term ω + Cash ω), ?_, ?_, ?_, ?_, rfl⟩
  · intro k
    exact hτstop
  · intro k ω
    exact le_refl _
  · intro k ω
    change Term ω + Cash ω = _
    rw [hTerm ω, hW ω, hCash ω]
  · intro k
    exact hTermI.add hCashI
