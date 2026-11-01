-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_killed_reward_joint_height_barrier_on_path_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:57:50.156513+00:00
-- url     : https://prove2.me/submissions/e32f2301-2149-4f92-b9f2-db4b13404cdb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_first_record_height_clock_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_reflected_ruin_barrier_level_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

/-- At each original path the actual killed reward is Borel in both levels. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (ω : Ω) :
    Measurable (fun p : ℝ × ℝ =>
      if twoSidedExitUpTime X p.1 ω < barrierRuinTime X p.2 ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X p.1 ω).toReal)))
      else 0) := by
  have hT : Measurable (fun p : ℝ × ℝ => twoSidedExitUpTime X p.1 ω) :=
    (avram_wave4_01_original_first_record_height_clock_measurable X ω).comp
      measurable_fst
  have hD : Measurable (fun p : ℝ × ℝ => barrierRuinTime X p.2 ω) :=
    (avram_wave4_01_original_reflected_ruin_barrier_level_measurable X ω).comp
      measurable_snd
  have hTime : Measurable (fun p : ℝ × ℝ =>
      (twoSidedExitUpTime X p.1 ω).toReal) :=
    ENNReal.measurable_toReal.comp hT
  have hExp : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (Real.exp (-(q *
        (twoSidedExitUpTime X p.1 ω).toReal)))) :=
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp ((measurable_const.mul hTime).neg))
  exact Measurable.ite (measurableSet_lt hT hD) hExp measurable_const
