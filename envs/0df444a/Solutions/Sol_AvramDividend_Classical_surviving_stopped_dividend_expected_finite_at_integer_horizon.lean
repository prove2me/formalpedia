-- Prove2me | solution 1 for AvramDividend.Classical.surviving_stopped_dividend_expected_finite_at_integer_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:05:38.490645+00:00
-- url     : https://prove2.me/submissions/9fbed454-5dc8-41cb-a355-ca7005363d90

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_levy_nat_horizon_integrable_of_standing
import Theorems.Thm_AvramDividend_Classical_surviving_stopped_dividend_expected_finite_of_integrable_levy_reserve

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Survival through an integer time makes earlier Stieltjes payouts integrable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : Ω → ℝ≥0∞)
    (T : ℝ≥0) (n : ℕ) (hT : T < (n : ℝ≥0)) :
    (∫⁻ ω, if ((n : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω then
      (∫⁻ r in paymentTimes (σ ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω))
      else 0 ∂P) ≠ ⊤ := by
  haveI : IsProbabilityMeasure P := X.isProbability
  have hXn := levy_nat_horizon_integrable_of_standing X hX n
  have hSum : Integrable (fun ω => x + X.X (n : ℝ≥0) ω) P :=
    (integrable_const x).add hXn
  exact surviving_stopped_dividend_expected_finite_of_integrable_levy_reserve
    X x D hD q hq σ T (n : ℝ≥0) hT hSum
