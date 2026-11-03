-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_08_actual_stopped_cash_from_one_sided_ito_data
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:39:04.580036+00:00
-- url     : https://prove2.me/submissions/95da2f0e-33bc-4e1f-9111-6774d14ddeeb

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_source_one_sided_hjb_budget_from_measurable_ito
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n)
    (τ : Ω → ℝ≥0)
    (hτEq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτStop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term M G H : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashMeas : AEStronglyMeasurable Cash P)
    (hMI : Integrable M P) (hGI : Integrable G P) (hHI : Integrable H P)
    (hMzero : (∫ ω, M ω ∂P) = 0)
    (hGHnonpos : ∀ᵐ ω ∂P, G ω + H ω ≤ 0)
    (hUpper : ∀ᵐ ω ∂P,
      Term ω + Cash ω ≤ w x + M ω + G ω + H ω) :
    (∫⁻ ω, ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
      Iic (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  have hclock :=
    avram_wave7_08_source_truncated_clock_nnreal_bounds X x D n
  have hτBound : ∀ ω, τ ω ≤ (n : ℝ≥0) := by
    intro ω
    rw [hτEq ω]
    exact hclock.2.1 ω
  have hτruin : ∀ ω, (τ ω : ℝ≥0∞) ≤ ruinTime X x D ω := by
    intro ω
    rw [hτEq ω]
    exact hclock.2.2 ω
  have hSmooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :=
    ⟨fun _ => hw_smooth, fun h => (hBV h).elim⟩
  have hbudget :=
    avram_wave6_06_original_source_one_sided_hjb_budget_from_measurable_ito
      X q hq w C hC hw0 hw_cont hw_neg hSmooth hw_gen hw_grad
      x (le_of_lt hx) hxc D hD τ (n : ℝ≥0)
      hτBound hτStop hτruin W Cash Term M G H
      hW hCash hTerm hTermMeas hCashMeas
      hMI hGI hHI hMzero hGHnonpos hUpper
  have hτfun :
      τ = fun ω => (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal :=
    funext hτEq
  simpa only [hτfun] using hbudget.2.2.2
