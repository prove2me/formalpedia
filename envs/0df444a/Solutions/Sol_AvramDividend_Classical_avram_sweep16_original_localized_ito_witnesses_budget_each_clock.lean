-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_original_localized_ito_witnesses_budget_each_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:17:30.184149+00:00
-- url     : https://prove2.me/submissions/17b9d67d-50f6-4bc5-af60-fea0f351c6a1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_one_sided_hjb_expected_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-! An exact local physical Ito ledger with centred integrable stopped M
    supplies each closed-clock original Stieltjes budget, including atoms. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : (¬ X.BoundedVariation →
      ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
      ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (S : ℕ → Ω → ℝ≥0∞)
    (τ : ℕ → Ω → ℝ≥0)
    (hτeq : ∀ k ω, τ k ω =
      (min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)).toNNReal)
    (hτbound : ∀ k ω, τ k ω ≤ (n : ℝ≥0))
    (hτstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (τ k ω : WithTop ℝ≥0)))
    (hτruin : ∀ k ω, (τ k ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (hResidual : ∀ k : ℕ, ∃ W Cash Term M G H : Ω → ℝ,
      (∀ ω, W ω = if τ k ω = 0 ∨
        (τ k ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ k ω) ω - rightLimit D (τ k ω) ω
        else riskProcess X x D (τ k ω) ω) ∧
      (∀ ω, Cash ω =
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) ∧
      (∀ ω, Term ω = Real.exp (-(q * (τ k ω : ℝ))) * w (W ω)) ∧
      Integrable Term P ∧ Integrable Cash P ∧
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + M ω + G ω + H ω)) :
    ∀ k : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iic (((min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)).toNNReal : ℝ)),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  intro k
  obtain ⟨W, Cash, Term, M, G, H, hW, hCash, hTerm,
    hTermI, hCashI, hMI, hGI, hHI, hMzero, hGH, hUpper⟩ :=
    hResidual k
  have hResult :=
    avram_wave6_06_original_one_sided_hjb_expected_budget
      X q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD (τ k) (n : ℝ≥0)
      (hτbound k) (hτstop k) (hτruin k)
      W Cash Term M G H
      hW hCash hTerm hTermI hCashI hMI hGI hHI hMzero hGH hUpper
  simpa only [hτeq k] using hResult.2.2.2
