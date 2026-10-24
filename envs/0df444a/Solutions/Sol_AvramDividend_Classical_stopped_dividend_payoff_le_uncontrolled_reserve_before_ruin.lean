-- Prove2me | solution 1 for AvramDividend.Classical.stopped_dividend_payoff_le_uncontrolled_reserve_before_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:38:40.358974+00:00
-- url     : https://prove2.me/submissions/fe18893d-69d5-455b-9e81-dcb1847607a7

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonneg_before_ruin
import Theorems.Thm_AvramDividend_Classical_local_verification_truncated_stieltjes_le_future_cumulative_dividends
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (σ : ℝ≥0∞)
    (T S : ℝ≥0) (hTS : T < S)
    (hSurv : (S : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ r in paymentTimes σ ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω)) ≤
    ENNReal.ofReal (x + X.X S ω) := by
  have hreserve := riskProcess_nonneg_before_ruin X x D ω S hSurv
  change 0 ≤ x + X.X S ω - D S ω at hreserve
  have hcapital : D S ω ≤ x + X.X S ω := by
    linarith
  calc
    (∫⁻ r in paymentTimes σ ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω)) ≤
        ENNReal.ofReal (D S ω) :=
      local_verification_truncated_stieltjes_le_future_cumulative_dividends
        D hD ω q hq σ T S hTS
    _ ≤ ENNReal.ofReal (x + X.X S ω) :=
      ENNReal.ofReal_le_ofReal hcapital
