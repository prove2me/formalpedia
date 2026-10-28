-- Prove2me | solution 1 for AvramDividend.Classical.dividendValue_le_of_expected_derivative_stochastic_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:55:08.427572+00:00
-- url     : https://prove2.me/submissions/f847c5c1-d308-4ad0-ae45-d2db15338592

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_dividendValue_le_iSup_expected_derivative_weighted
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The finite-horizon derivative-weighted stopped stochastic budget implies the full dividend verification inequality via the proved Stieltjes comparison and an upper bound on a supremum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (hq : 0 ≤ q)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissible X x D)
    (hStrat : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (u : Ω → ℝ → ℝ)
    (hgrad : ∀ ω t, t ∈ paymentTimes (ruinTime X x D ω) →
      1 ≤ deriv w (u ω t))
    (hWeighted : ∀ n : ℕ, ∀ ω : Ω,
      IntegrableOn (fun t : ℝ =>
        Real.exp (-(q * t)) * deriv w (u ω t))
        (paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ))
        (dividendMeasure D ω))
    (hBudget : ∀ n : ℕ,
      (∫⁻ ω, ENNReal.ofReal
        (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
          Real.exp (-(q * t)) * deriv w (u ω t)
            ∂(dividendMeasure D ω)) ∂P) ≤ ENNReal.ofReal (w x)) :
    dividendValue X q x D ≤ ENNReal.ofReal (w x) := by
  exact
    (dividendValue_le_iSup_expected_derivative_weighted
      (P := P) X q hq x D hD hStrat w u hgrad hWeighted).trans
      (iSup_le hBudget)
