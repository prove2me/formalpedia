-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_dividendValue_le_full_preruin_undiscounted_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:16:40.957202+00:00
-- url     : https://prove2.me/submissions/fdbe4cab-3806-4300-9c9e-3d5289fb497e

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_discounted_stieltjes_lintegral_le_measure
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The genuine expected source payout is bounded by the total source
    Stieltjes mass of the original full strict pre-ruin payment region. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (q : ℝ) (hq : 0 ≤ q) :
    dividendValue X q x D ≤
      (∫⁻ ω : Ω,
        (dividendMeasure D ω) (paymentTimes (ruinTime X x D ω)) ∂P) := by
  change (∫⁻ ω : Ω,
      ∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω : Ω,
      (dividendMeasure D ω) (paymentTimes (ruinTime X x D ω)) ∂P)
  apply MeasureTheory.lintegral_mono
  intro ω
  exact discounted_stieltjes_lintegral_le_measure q hq
    (dividendMeasure D ω) (paymentTimes (ruinTime X x D ω))
    (paymentTimes_measurable _)
    (fun t ht => ht.1)
