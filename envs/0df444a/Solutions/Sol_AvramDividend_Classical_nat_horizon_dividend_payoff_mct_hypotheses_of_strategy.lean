-- Prove2me | solution 1 for AvramDividend.Classical.nat_horizon_dividend_payoff_mct_hypotheses_of_strategy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T15:14:10.578666+00:00
-- url     : https://prove2.me/submissions/bd2a6514-ace8-4126-92bf-90ea67932402

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_nat_horizon_dividend_payoff_mono_tendsto
import Theorems.Thm_AvramDividend_Classical_nat_horizon_dividend_payoff_aemeasurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    (∀ n : ℕ, AEMeasurable
      (fun ω => ∫⁻ t in
        paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) P) ∧
    (∀ᵐ ω ∂P, Monotone (fun n : ℕ =>
      ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) ∧
    (∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ =>
        ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      atTop
      (𝓝 (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)))) := by
  rcases nat_horizon_dividend_payoff_mono_tendsto X q x D with ⟨hmono, htend⟩
  refine ⟨nat_horizon_dividend_payoff_aemeasurable X q x D hD, ?_, ?_⟩
  · exact Filter.Eventually.of_forall hmono
  · exact Filter.Eventually.of_forall htend
