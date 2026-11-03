-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_same_measure_finite_horizon_inner_and_outer_real_integrability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:47:52.453194+00:00
-- url     : https://prove2.me/submissions/3558de1a-54f9-4d46-9c01-fa12ae4f031b

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_paymentWindow_finite_of_strategy
import Theorems.Thm_AvramDividend_Classical_discounted_stieltjes_integrableOn_of_finite_measure
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_real_horizon_signed_stieltjes_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The genuine finite source Stieltjes dividend reward is integrable
    on every path and its real signed payout is L1 under the original P. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) :
    (∀ ω : Ω, IntegrableOn (fun t : ℝ => Real.exp (-(q * t)))
      (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ))
      (dividendMeasure D ω)) ∧
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P := by
  constructor
  · intro ω
    have hMass := dividendMeasure_paymentWindow_finite_of_strategy
      D hD.1.1 ω (ruinTime X x D ω) T
    exact discounted_stieltjes_integrableOn_of_finite_measure
      q hq (dividendMeasure D ω)
      (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ))
      ((paymentTimes_measurable _).inter measurableSet_Iic)
      (fun t ht => ht.1.1) hMass
  · exact avram_wave7_03_original_real_horizon_signed_stieltjes_integrable
      X x C D hD q hq (T : ℝ) T.property
