-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_discountedPayoff_zero_outside_controlledUpExit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T18:23:58.763991+00:00
-- url     : https://prove2.me/submissions/57401db1-199c-49f8-8c4b-24bbae938119

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_discountedDividend_zero_if_ruin_before_upcrossing
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_discountedPayoff_zero_if_upcrossing_infinite
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The barrier pays no discounted dividends on paths that do not
    reach the upper barrier strictly before controlled ruin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x a : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω)
    (hkill : ¬
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)) <
        ruinTime X x (barrierStrategy X x a) ω) :
    (∫⁻ t in paymentTimes
        (ruinTime X x (barrierStrategy X x a) ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure (barrierStrategy X x a) ω)) = 0 := by
  let τ : ℝ≥0∞ :=
    ⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)
  change ¬ τ < ruinTime X x (barrierStrategy X x a) ω at hkill
  by_cases htop : τ = ⊤
  · apply barrierStrategy_discountedPayoff_zero_if_upcrossing_infinite
      X q x a hx0 hxa ω
    simpa only [τ] using htop
  · let u : ℝ≥0 := τ.toNNReal
    have hu : (u : ℝ≥0∞) = τ := ENNReal.coe_toNNReal htop
    apply barrierStrategy_discountedDividend_zero_if_ruin_before_upcrossing
      X q x a hx0 hxa ω u
    · simpa only [τ] using hu
    · rw [hu]
      exact le_of_not_gt hkill