-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_killed_record_reward_joint_height_path_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:49:46.379525+00:00
-- url     : https://prove2.me/submissions/fbd6f431-6f0f-40c5-925e-eef9499485d3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_first_record_clock_joint_height_path_measurable
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

/-- The actual killed record reward is product-measurable in height and path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q a : ℝ) :
    Measurable (fun p : ℝ × Ω =>
      if twoSidedExitUpTime X p.1 p.2 < barrierRuinTime X a p.2 then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X p.1 p.2).toReal)))
      else 0) := by
  have hT : Measurable (fun p : ℝ × Ω =>
      twoSidedExitUpTime X p.1 p.2) :=
    avram_wave4_01_original_first_record_clock_joint_height_path_measurable X
  have hR : Measurable (fun p : ℝ × Ω =>
      barrierRuinTime X a p.2) :=
    (barrierRuinTime_measurable X a).comp measurable_snd
  have hTime : Measurable (fun p : ℝ × Ω =>
      (twoSidedExitUpTime X p.1 p.2).toReal) :=
    ENNReal.measurable_toReal.comp hT
  have hExp : Measurable (fun p : ℝ × Ω =>
      ENNReal.ofReal (Real.exp (-(q *
        (twoSidedExitUpTime X p.1 p.2).toReal)))) :=
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp ((measurable_const.mul hTime).neg))
  exact hExp.ite (measurableSet_lt hT hR) measurable_const
