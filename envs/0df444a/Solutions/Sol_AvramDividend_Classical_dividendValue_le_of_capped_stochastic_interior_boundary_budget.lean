-- Prove2me | solution 1 for AvramDividend.Classical.dividendValue_le_of_capped_stochastic_interior_boundary_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:09:49.031415+00:00
-- url     : https://prove2.me/submissions/444f3406-b422-43fc-8638-3e97b4caf88a

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_dividendValue_eq_iSup_truncated
import Theorems.Thm_AvramDividend_Classical_expected_capped_hjb_payment_weighted_interior_boundary
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A uniform stopped stochastic budget for interior derivative-weighted dividends together with the exact boundary Stieltjes remainder proves the complete infinite-horizon dividend-value estimate, without requiring derivative integrability or atomic dividends. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (hStrat : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
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
  rw [dividendValue_eq_iSup_truncated X q x D hD]
  refine iSup_le fun n => ?_
  have hn :=
    expected_capped_hjb_payment_weighted_interior_boundary
      (P := P) X D hStrat q w C hw_hjb
      (fun ω => ruinTime X x D ω) (n : ℝ≥0) u hInterior
  have hle := (show
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      (∫⁻ ω,
        (∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ)) ∩
          {t : ℝ | 0 < u ω t ∧ ENNReal.ofReal (u ω t) < C},
          ENNReal.ofReal (Real.exp (-(q * t)) * deriv w (u ω t))
            ∂(dividendMeasure D ω)) +
        (∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ)) \
          {t : ℝ | 0 < u ω t ∧ ENNReal.ofReal (u ω t) < C},
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)) ∂P) from by
        simpa only [NNReal.coe_natCast] using hn)
  exact hle.trans (hBudget n)
