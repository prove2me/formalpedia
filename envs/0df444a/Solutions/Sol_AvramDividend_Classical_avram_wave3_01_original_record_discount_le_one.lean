-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_01_original_record_discount_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T22:22:34.76625+00:00
-- url     : https://prove2.me/submissions/7f39724e-61e4-41d1-976d-41decafeaee6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The true discounted first-record reward is bounded by unit mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) :
    ∀ a h : ℝ,
      (∫⁻ ω, if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P) ≤ 1 := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro a h
  have hpt (ω : Ω) :
      (if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
      else 0) ≤ (1 : ℝ≥0∞) := by
    split_ifs
    · have ht : 0 ≤ (twoSidedExitUpTime X h ω).toReal :=
        ENNReal.toReal_nonneg
      have hqt : 0 ≤ q * (twoSidedExitUpTime X h ω).toReal :=
        mul_nonneg hq.le ht
      have he : Real.exp
          (-(q * (twoSidedExitUpTime X h ω).toReal)) ≤ 1 := by
        simpa only [Real.exp_zero] using
          (Real.exp_le_exp.mpr (neg_nonpos.mpr hqt))
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal he
    · exact zero_le_one
  calc
    (∫⁻ ω, if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
      ENNReal.ofReal
        (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
    else 0 ∂P) ≤ ∫⁻ _ : Ω, (1 : ℝ≥0∞) ∂P :=
      lintegral_mono hpt
    _ = 1 := by simp
