-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_killed_reward_joint_height_depth_law_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T17:40:07.40848+00:00
-- url     : https://prove2.me/submissions/494f36fa-c612-4e9d-93f7-8b8bc4a81011

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_killed_reward_joint_height_depth_path_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

/-- The original killed record discount law is jointly Borel in all real height-depth pairs. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) :
    Measurable (fun p : ℝ × ℝ =>
      ∫⁻ ω, if twoSidedExitUpTime X p.1 ω <
                 barrierRuinTime X p.2 ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X p.1 ω).toReal)))
      else 0 ∂P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hJoint : Measurable (fun z : (ℝ × ℝ) × Ω =>
      if twoSidedExitUpTime X z.1.1 z.2 <
           barrierRuinTime X z.1.2 z.2 then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X z.1.1 z.2).toReal)))
      else 0) :=
    avram_wave4_01_original_killed_reward_joint_height_depth_path_measurable X q
  exact hJoint.lintegral_prod_right
