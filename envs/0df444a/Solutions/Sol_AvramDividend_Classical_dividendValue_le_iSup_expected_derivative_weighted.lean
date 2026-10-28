-- Prove2me | solution 1 for AvramDividend.Classical.dividendValue_le_iSup_expected_derivative_weighted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:42:46.058648+00:00
-- url     : https://prove2.me/submissions/950a00d5-8558-4848-91b9-8a16dcdc3145

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_dividendValue_eq_iSup_truncated
import Theorems.Thm_AvramDividend_Classical_expected_discounted_actual_dividend_le_derivative_weighted

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- For an admissible dividend strategy, the full infinite-horizon expected discounted dividend value is bounded by the supremum of finite-horizon expected derivative-weighted real Stieltjes integrals. It combines the proved monotone truncation identity for dividendValue with the actual-strategy expected derivative-weighted payment inequality, without needing the missing stopped Levy chain rule. -/
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
        (dividendMeasure D ω)) :
    dividendValue X q x D ≤
      ⨆ n : ℕ, ∫⁻ ω, ENNReal.ofReal
        (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
          Real.exp (-(q * t)) * deriv w (u ω t)
            ∂(dividendMeasure D ω)) ∂P := by
  rw [dividendValue_eq_iSup_truncated X q x D hD]
  refine iSup_le fun n => ?_
  have hn :=
    expected_discounted_actual_dividend_le_derivative_weighted
      (P := P) D hStrat q hq (fun ω => ruinTime X x D ω) (n : ℝ≥0) w u
      (fun ω t ht => hgrad ω t ht.1)
      (fun ω => by simpa only [NNReal.coe_natCast] using hWeighted n ω)
  have hle := (show
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      (∫⁻ ω, ENNReal.ofReal
        (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
          Real.exp (-(q * t)) * deriv w (u ω t)
            ∂(dividendMeasure D ω)) ∂P) from by
        simpa only [NNReal.coe_natCast] using hn)
  exact hle.trans (le_iSup_of_le n le_rfl)
