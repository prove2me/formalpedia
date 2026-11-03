-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_zero_discount_value_eq_full_preruin_stieltjes_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:20:53.904506+00:00
-- url     : https://prove2.me/submissions/5b0f5d43-1576-494b-b921-44e2b7f124f0

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Zero discount counts precisely all original pre-ruin dividend measure
    mass, including the special payment atom at time zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) :
    dividendValue X 0 x D =
      (∫⁻ ω : Ω,
        (dividendMeasure D ω) (paymentTimes (ruinTime X x D ω)) ∂P) := by
  change (∫⁻ ω : Ω,
    ∫⁻ t in paymentTimes (ruinTime X x D ω),
      ENNReal.ofReal (Real.exp (-(0 * t))) ∂(dividendMeasure D ω) ∂P) =
    (∫⁻ ω : Ω,
      (dividendMeasure D ω) (paymentTimes (ruinTime X x D ω)) ∂P)
  simp only [zero_mul, neg_zero, Real.exp_zero, ENNReal.ofReal_one,
    MeasureTheory.lintegral_one]
  simp
