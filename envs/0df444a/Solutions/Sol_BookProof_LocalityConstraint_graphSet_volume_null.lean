-- Prove2me | solution 1 for BookProof.LocalityConstraint.graphSet_volume_null
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:39:44.141858+00:00
-- url     : https://prove2.me/submissions/c768d9f9-e5c9-4933-9d58-5bab1f7a37bc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterLocalityConstraintNull.lean — solution of BookProof.LocalityConstraint.graphSet_volume_null
import Mathlib
import Definitions.Def_ChapterLocalityConstraintNull
import Theorems.Thm_BookProof_LocalityConstraint_graphSet_null
open BookProof.LocalityConstraint




open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {α : Type*} [MeasurableSpace α]

variable {α : Type*} [MeasurableSpace α]

set_option maxHeartbeats 1000000 in
theorem solution {f : ℝ → ℝ} (hf : Measurable f) :
    (volume : Measure (ℝ × ℝ)) (graphSet f) = 0 := by

  rw [Measure.volume_eq_prod]
  exact graphSet_null _ _ hf
