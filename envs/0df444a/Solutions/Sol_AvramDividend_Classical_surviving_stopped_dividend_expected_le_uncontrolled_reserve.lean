-- Prove2me | solution 1 for AvramDividend.Classical.surviving_stopped_dividend_expected_le_uncontrolled_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:39:38.544439+00:00
-- url     : https://prove2.me/submissions/e63ea073-ad1c-4bfb-8648-8b928e22ef02

import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonneg_before_ruin
import Theorems.Thm_AvramDividend_Classical_local_verification_truncated_stieltjes_le_future_cumulative_dividends
import Mathlib.Analysis.Complex.Exponential

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
    (q : ℝ) (hq : 0 ≤ q) (σ : Ω → ℝ≥0∞)
    (T S : ℝ≥0) (hTS : T < S) :
    (∫⁻ ω, if (S : ℝ≥0∞) < ruinTime X x D ω then
      (∫⁻ r in paymentTimes (σ ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω))
      else 0 ∂P) ≤
    (∫⁻ ω, ENNReal.ofReal (x + X.X S ω) ∂P) := by
  apply lintegral_mono
  intro ω
  by_cases hSurv : (S : ℝ≥0∞) < ruinTime X x D ω
  · simp only [if_pos hSurv]
    have hreserve := riskProcess_nonneg_before_ruin X x D ω S hSurv
    change 0 ≤ x + X.X S ω - D S ω at hreserve
    have hDle : D S ω ≤ x + X.X S ω := by
      linarith
    exact (local_verification_truncated_stieltjes_le_future_cumulative_dividends
      D hD ω q hq (σ ω) T S hTS).trans
      (ENNReal.ofReal_le_ofReal hDle)
  · simp [hSurv]
