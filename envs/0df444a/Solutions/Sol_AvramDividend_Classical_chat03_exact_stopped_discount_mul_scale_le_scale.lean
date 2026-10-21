-- Prove2me | solution 1 for AvramDividend.Classical.chat03_exact_stopped_discount_mul_scale_le_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T08:37:51.950952+00:00
-- url     : https://prove2.me/submissions/100989dc-b1f9-4127-ac17-f7f6675730f0

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_discounted_upperfirst_lintegral_le_one
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-!
The entire left side of the stopped-scale identity is bounded by its
terminal scale value, without invoking optional stopping.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (lower upper wa : ℝ) :
    (∫⁻ ω,
      if twoSidedExitUpTime X upper ω <
          twoSidedExitDownTime X lower ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (twoSidedExitUpTime X upper ω))))
      else 0 ∂P) * ENNReal.ofReal wa ≤ ENNReal.ofReal wa := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hI : (∫⁻ ω,
      if twoSidedExitUpTime X upper ω <
          twoSidedExitDownTime X lower ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (twoSidedExitUpTime X upper ω))))
      else 0 ∂P) ≤ 1 :=
    chat03_discounted_upperfirst_lintegral_le_one P q hq
      (fun ω => twoSidedExitUpTime X upper ω)
      (fun ω => twoSidedExitDownTime X lower ω)
  calc
    _ ≤ (1 : ℝ≥0∞) * ENNReal.ofReal wa :=
      mul_le_mul_left hI _
    _ = ENNReal.ofReal wa := one_mul _
