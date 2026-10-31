-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_01_original_record_toReal_semigroup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T22:28:18.187382+00:00
-- url     : https://prove2.me/submissions/e7289f7a-1880-4e91-b2f6-dbb6de08cb48

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_uncapped_reflected_record_discount_semigroup
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Exact real-valued genuine first-record multiplicative law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b c q : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hq : 0 < q) :
    (∫⁻ ω, if twoSidedExitUpTime X (b + c) ω < barrierRuinTime X a ω then
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X (b + c) ω).toReal)))
    else 0 ∂P).toReal =
      (∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω then
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal)))
    else 0 ∂P).toReal * (∫⁻ ω, if twoSidedExitUpTime X c ω < barrierRuinTime X a ω then
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X c ω).toReal)))
    else 0 ∂P).toReal := by
  have h := avram_wave3_01_uncapped_reflected_record_discount_semigroup
    X a b c q ha hb hc hq
  simpa only [ENNReal.toReal_mul] using congrArg ENNReal.toReal h
