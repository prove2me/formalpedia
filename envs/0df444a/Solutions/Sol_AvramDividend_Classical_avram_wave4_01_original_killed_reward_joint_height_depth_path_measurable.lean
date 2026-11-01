-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_killed_reward_joint_height_depth_path_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T17:33:05.673589+00:00
-- url     : https://prove2.me/submissions/32de8e2e-efed-4b35-93c6-d1ac9d7231e5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_first_record_clock_joint_height_path_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_reflected_ruin_joint_barrier_path_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

/-- Actual killed record reward is jointly Borel in height, depth and path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) :
    Measurable (fun p : (ℝ × ℝ) × Ω =>
      if twoSidedExitUpTime X p.1.1 p.2 < barrierRuinTime X p.1.2 p.2 then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X p.1.1 p.2).toReal)))
      else 0) := by
  have hh : Measurable (fun p : (ℝ × ℝ) × Ω => p.1.1) :=
    measurable_fst.comp measurable_fst
  have ha : Measurable (fun p : (ℝ × ℝ) × Ω => p.1.2) :=
    measurable_snd.comp measurable_fst
  have hω : Measurable (fun p : (ℝ × ℝ) × Ω => p.2) := measurable_snd
  have hT : Measurable (fun p : (ℝ × ℝ) × Ω =>
      twoSidedExitUpTime X p.1.1 p.2) :=
    (avram_wave4_01_original_first_record_clock_joint_height_path_measurable X).comp
      (hh.prodMk hω)
  have hD : Measurable (fun p : (ℝ × ℝ) × Ω =>
      barrierRuinTime X p.1.2 p.2) :=
    (avram_wave4_01_original_reflected_ruin_joint_barrier_path_measurable X).comp
      (ha.prodMk hω)
  have hTime : Measurable (fun p : (ℝ × ℝ) × Ω =>
      (twoSidedExitUpTime X p.1.1 p.2).toReal) :=
    ENNReal.measurable_toReal.comp hT
  have hExp : Measurable (fun p : (ℝ × ℝ) × Ω =>
      ENNReal.ofReal
        (Real.exp (-(q * (twoSidedExitUpTime X p.1.1 p.2).toReal)))) :=
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp ((measurable_const.mul hTime).neg))
  exact Measurable.ite (measurableSet_lt hT hD) hExp measurable_const
