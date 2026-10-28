-- Prove2me | solution 1 for AvramDividend.Classical.expected_stopped_dividend_le_levy_on_survival_event
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T15:13:38.261026+00:00
-- url     : https://prove2.me/submissions/3ab89d6d-9f07-4c1f-9be2-e39a2fe48223

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_stopped_dividend_payoff_le_uncontrolled_reserve_before_ruin
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Expectation localisation of actual stopped Stieltjes dividends on surviving paths. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : ℝ≥0∞)
    (T S : ℝ≥0) (hTS : T < S)
    (E : Set Ω) (hE : MeasurableSet E)
    (hSurv : ∀ ω ∈ E, (S : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ ω in E, ∫⁻ r in paymentTimes σ ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω in E, ENNReal.ofReal (x + X.X S ω) ∂P) := by
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem hE] with ω hω
  exact stopped_dividend_payoff_le_uncontrolled_reserve_before_ruin
    X x D hD ω q hq σ T S hTS (hSurv ω hω)
