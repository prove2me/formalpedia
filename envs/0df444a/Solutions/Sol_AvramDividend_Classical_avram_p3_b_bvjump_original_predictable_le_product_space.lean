-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_predictable_le_product_space
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:44:56.176291+00:00
-- url     : https://prove2.me/submissions/e240b09e-5422-4547-bfc9-573fbb58640a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original filtration's predictable sigma algebra is a subspace of the
ordinary time-path product sigma algebra, so the physical clock can be trimmed. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ) :
    𝓕.rightCont.predictable ≤
      (inferInstance : MeasurableSpace (ℝ≥0 × Ω)) := by
  apply measurableSpace_le_predictable_of_measurableSet
  · intro A hA
    exact (MeasurableSet.singleton (0 : ℝ≥0)).prod
      ((𝓕.rightCont.le 0) A hA)
  · intro i A hA
    exact measurableSet_Ioi.prod ((𝓕.rightCont.le i) A hA)
