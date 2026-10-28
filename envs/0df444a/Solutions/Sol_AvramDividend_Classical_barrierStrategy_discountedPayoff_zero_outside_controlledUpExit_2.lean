-- Prove2me | solution 2 for AvramDividend.Classical.barrierStrategy_discountedPayoff_zero_outside_controlledUpExit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T18:24:23.758703+00:00
-- url     : https://prove2.me/submissions/4d3e101c-c5bc-450e-801e-51fceefcbeaf

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_discountedDividend_zero_if_ruin_before_upcrossing
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_discountedPayoff_zero_if_upcrossing_infinite

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
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
  by_cases htop : (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)) = ⊤
  · exact AvramDividend.Classical.barrierStrategy_discountedPayoff_zero_if_upcrossing_infinite
      X q x a hx0 hxa ω htop
  · obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.1 htop
    exact AvramDividend.Classical.barrierStrategy_discountedDividend_zero_if_ruin_before_upcrossing
      X q x a hx0 hxa ω u hu (by have := not_lt.1 hkill; rwa [← hu] at this)
