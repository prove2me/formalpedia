-- Prove2me | solution 1 for BookProof.LocalityConstraint.not_isProbabilityMeasure_restrict_graphSet
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:41:03.00699+00:00
-- url     : https://prove2.me/submissions/5ba0d4a3-3cc7-4a58-8ac1-9b688ef4a5d7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterLocalityConstraintNull.lean — solution of BookProof.LocalityConstraint.not_isProbabilityMeasure_restrict_graphSet
import Mathlib
import Definitions.Def_ChapterLocalityConstraintNull
import Theorems.Thm_BookProof_LocalityConstraint_restrict_graphSet_eq_zero
open BookProof.LocalityConstraint




open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {α : Type*} [MeasurableSpace α]

variable {α : Type*} [MeasurableSpace α]

set_option maxHeartbeats 1000000 in
theorem solution (μ : Measure α) (ν : Measure ℝ)
    [SFinite ν] [NullSingletonClass ν] {f : α → ℝ} (hf : Measurable f) :
    ¬ IsProbabilityMeasure ((μ.prod ν).restrict (graphSet f)) := by

  intro h
  have h1 : ((μ.prod ν).restrict (graphSet f)) Set.univ = 1 := h.measure_univ
  rw [restrict_graphSet_eq_zero μ ν hf] at h1
  simp at h1
