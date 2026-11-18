-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB49_original_barrier_upperstrip_section_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:29:08.146698+00:00
-- url     : https://prove2.me/submissions/8e287d5d-fe05-47a4-9370-2e230724cda3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_isDividendStrategy_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_avram_gfinite67_original_real_time_cap_strip_joint_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/-- Every original cap-barrier upper-strip time section is Lebesgue-measurable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (ω : Ω) :
    MeasurableSet {t : ℝ | t < (T : ℝ) ∧
      (5 / 44 : ℝ) < riskProcess X (1 / 8 : ℝ)
        (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ))
        (Real.toNNReal t) ω} := by
  have hD : IsDividendStrategy 𝓕
      (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) :=
    barrierStrategy_isDividendStrategy_nonnegative_barrier X
      (1 / 8 : ℝ) (1 / 8 : ℝ) (by norm_num) (by norm_num)
  have hStop : IsStoppingTime 𝓕.rightCont
      (fun _ : Ω => (T : WithTop ℝ≥0)) :=
    by simpa using (isStoppingTime_const 𝓕.rightCont T)
  have hJoint :=
    avram_gfinite67_original_real_time_cap_strip_joint_measurable
      X (1 / 8 : ℝ)
      (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ))
      hD (fun _ : Ω => T) hStop (5 / 44 : ℝ)
  have hPair : Measurable (fun t : ℝ => (t, ω)) :=
    measurable_id.prodMk measurable_const
  simpa only [Set.preimage, Set.mem_setOf_eq] using (hPair hJoint)
