-- Prove2me | solution 1 for AvramDividend.Classical.admissibleCap_dividendValue_le_of_gradient_stochastic_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:58:14.700791+00:00
-- url     : https://prove2.me/submissions/9c9101f6-f249-4fa6-9ab6-e7ed4c8e58a2

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_dividendValue_le_of_gradient_stochastic_interior_boundary_budget
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The gradient-only stochastic budget bound with native capped-admissibility, matching the bounded-variation verification hypothesis without an HJB maximum equality. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (hq : 0 ≤ q)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (C : ℝ≥0∞)
    (hD : IsAdmissibleLe X x C D) (w : ℝ → ℝ)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (u : Ω → ℝ → ℝ)
    (hInterior : ∀ ω, MeasurableSet
      {t : ℝ | 0 < u ω t ∧ ENNReal.ofReal (u ω t) < C})
    (hBudget : ∀ n : ℕ,
      (∫⁻ ω,
        (∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ)) ∩
          {t : ℝ | 0 < u ω t ∧ ENNReal.ofReal (u ω t) < C},
          ENNReal.ofReal (Real.exp (-(q * t)) * deriv w (u ω t))
            ∂(dividendMeasure D ω)) +
        (∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ)) \
          {t : ℝ | 0 < u ω t ∧ ENNReal.ofReal (u ω t) < C},
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)) ∂P) ≤ ENNReal.ofReal (w x)) :
    dividendValue X q x D ≤ ENNReal.ofReal (w x) := by
  exact dividendValue_le_of_gradient_stochastic_interior_boundary_budget
    X q hq x D hD.1 hD.1.1 w C hw_grad u hInterior hBudget
