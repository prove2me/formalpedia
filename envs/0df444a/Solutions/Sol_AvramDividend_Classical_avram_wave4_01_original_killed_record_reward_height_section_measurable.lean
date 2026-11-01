-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_killed_record_reward_height_section_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:19:57.039182+00:00
-- url     : https://prove2.me/submissions/15ce8208-514c-4b14-b720-43a2eb5d954e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_mono_threshold
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

/-- Each original-path killed first-record reward is Borel measurable in height. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q a : ℝ) (ω : Ω) :
    Measurable (fun h : ℝ =>
      if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
          ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
        else 0) := by
  have hmono : Monotone (fun h : ℝ => twoSidedExitUpTime X h ω) := by
    intro b c hbc
    exact twoSidedExitUpTime_mono_threshold X b c hbc ω
  have hT : Measurable (fun h : ℝ => twoSidedExitUpTime X h ω) :=
    hmono.measurable
  have hR : Measurable (fun h : ℝ => (twoSidedExitUpTime X h ω).toReal) :=
    ENNReal.measurable_toReal.comp hT
  have hD : Measurable (fun h : ℝ =>
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))) := by
    exact ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp ((measurable_const.mul hR).neg))
  have hE : MeasurableSet {h : ℝ |
      twoSidedExitUpTime X h ω < barrierRuinTime X a ω} :=
    measurableSet_lt hT measurable_const
  exact Measurable.ite hE hD measurable_const
