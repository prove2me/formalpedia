-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_reflected_record_discount_strict_lt_one_of_root
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:40:27.168749+00:00
-- url     : https://prove2.me/submissions/1d496f53-7a2b-4fc5-a6aa-6744b5a62d17

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_reflected_record_discount_le_unrestricted_upcrossing_root

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The original strict first-record discount, even without reflected
killing, cannot equal one at positive height and positive root. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∀ a b : ℝ, 0 < b →
      (∫⁻ ω, if twoSidedExitUpTime X b ω <
                    barrierRuinTime X a ω then
          ENNReal.ofReal
            (Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal)))
        else 0 ∂P).toReal < 1 := by
  intro a b hb
  have hbound :=
    avram_wave4_01_reflected_record_discount_le_unrestricted_upcrossing_root
      X q hq φ hφ hroot a b hb
  have hreal : (∫⁻ ω, if twoSidedExitUpTime X b ω <
                    barrierRuinTime X a ω then
          ENNReal.ofReal
            (Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal)))
        else 0 ∂P).toReal ≤ Real.exp (-(φ * b)) := by
    have h := ENNReal.toReal_mono (by simp) hbound
    simpa only [ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _))] using h
  have hneg : -(φ * b) < 0 :=
    neg_lt_zero.mpr (mul_pos hφ hb)
  have hexp : Real.exp (-(φ * b)) < 1 := by
    simpa using (Real.exp_lt_exp.mpr hneg)
  exact lt_of_le_of_lt hreal hexp
