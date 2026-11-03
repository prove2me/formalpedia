-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_21_original_interior_discounted_cash_le_derivative_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:48:04.654705+00:00
-- url     : https://prove2.me/submissions/f9bd526d-d5f4-488b-afb9-e8c8c9af5b8b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_stieltjes_dividend_interior_gradient_nonpositive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Original Stieltjes continuous-payment cash is bounded by its gradient term
    on every measurable region of strictly interior reserves. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (ω : Ω) (A : Set ℝ) (hA : MeasurableSet A)
    (hregion : ∀ t ∈ A,
      0 < riskProcess X x D t.toNNReal ω ∧
      ENNReal.ofReal (riskProcess X x D t.toNNReal ω) < C)
    (hCash : IntegrableOn
      (fun t : ℝ => Real.exp (-(q * t)))
      A (dividendMeasure D ω))
    (hDeriv : IntegrableOn
      (fun t : ℝ => Real.exp (-(q * t)) *
        deriv w (riskProcess X x D t.toNNReal ω))
      A (dividendMeasure D ω)) :
    (∫ t in A, Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ≤
      (∫ t in A, Real.exp (-(q * t)) *
        deriv w (riskProcess X x D t.toNNReal ω)
        ∂(dividendMeasure D ω)) := by
  have hfun :
      (fun t : ℝ => Real.exp (-(q * t)) *
        (1 - deriv w (riskProcess X x D t.toNNReal ω))) =
      (fun t : ℝ => Real.exp (-(q * t)) -
        Real.exp (-(q * t)) *
          deriv w (riskProcess X x D t.toNNReal ω)) := by
    funext t
    ring
  have hInt : IntegrableOn
      (fun t : ℝ => Real.exp (-(q * t)) *
        (1 - deriv w (riskProcess X x D t.toNNReal ω)))
      A (dividendMeasure D ω) := by
    rw [hfun]
    exact hCash.sub hDeriv
  have hnonpos :=
    avram_wave7_02_original_stieltjes_dividend_interior_gradient_nonpositive
      X x D hD q w C hw_grad ω A hA hregion hInt
  rw [hfun, integral_sub hCash hDeriv] at hnonpos
  linarith
