-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_02a_joint_original_predictable_mark_lift_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:28:26.080988+00:00
-- url     : https://prove2.me/submissions/bf498e06-c1ff-4d0b-afba-07d7194ded8e

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ) :
    @Measurable ((ℝ≥0 × ℝ) × Ω) ((ℝ≥0 × Ω) × ℝ)
      (inferInstance : MeasurableSpace ((ℝ≥0 × ℝ) × Ω))
      (@Prod.instMeasurableSpace _ _ 𝓕.predictable
        (inferInstance : MeasurableSpace ℝ))
      (fun q : (ℝ≥0 × ℝ) × Ω => ((q.1.1, q.2), q.1.2)) := by
  have hpred : 𝓕.predictable ≤
      (inferInstance : MeasurableSpace (ℝ≥0 × Ω)) := by
    apply MeasureTheory.measurableSpace_le_predictable_of_measurableSet
    · intro A hA
      exact (measurableSet_singleton (⊥ : ℝ≥0)).prod ((𝓕.le ⊥) A hA)
    · intro i A hA
      exact measurableSet_Ioi.prod ((𝓕.le i) A hA)
  have hid : @Measurable (ℝ≥0 × Ω) (ℝ≥0 × Ω)
      (inferInstance : MeasurableSpace (ℝ≥0 × Ω))
      𝓕.predictable id :=
    measurable_id.mono le_rfl hpred
  exact (hid.comp (measurable_fst.fst.prodMk measurable_snd)).prodMk
    measurable_fst.snd
