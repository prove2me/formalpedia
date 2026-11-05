-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_e_compensator_original_rightCont_predictable_ambient_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:37:19.059522+00:00
-- url     : https://prove2.me/submissions/94668809-91d5-45e2-a022-a9eb33b8c524

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
{Ω : Type*} [mΩ : MeasurableSpace Ω]
{𝓕 : Filtration ℝ≥0 mΩ} (E : Set (ℝ≥0 × Ω))
(hE : MeasurableSet[𝓕.rightCont.predictable] E) :
MeasurableSet E := by
  have hle : 𝓕.rightCont.predictable ≤
      (inferInstance : MeasurableSpace (ℝ≥0 × Ω)) := by
    apply measurableSpace_le_predictable_of_measurableSet
    · intro A hA
      exact (measurableSet_singleton (⊥ : ℝ≥0)).prod
        ((𝓕.rightCont.le ⊥) A hA)
    · intro i A hA
      exact measurableSet_Ioi.prod ((𝓕.rightCont.le i) A hA)
  exact hle E hE
