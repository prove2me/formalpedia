-- Prove2me | solution 1 for BookProof.LocalityConstraint.restrict_graphSet_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:41:01.809618+00:00
-- url     : https://prove2.me/submissions/2ca6c699-bdcc-4643-8fce-6b3b8d9c7aba

-- Generated from ChapterLocalityConstraintNull.lean — solution of BookProof.LocalityConstraint.restrict_graphSet_eq_zero
import Mathlib
import Definitions.Def_ChapterLocalityConstraintNull
import Theorems.Thm_BookProof_LocalityConstraint_graphSet_null
open BookProof.LocalityConstraint




open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {α : Type*} [MeasurableSpace α]

variable {α : Type*} [MeasurableSpace α]

set_option maxHeartbeats 1000000 in
theorem solution (μ : Measure α) (ν : Measure ℝ) [SFinite ν] [NullSingletonClass ν]
    {f : α → ℝ} (hf : Measurable f) :
    (μ.prod ν).restrict (graphSet f) = 0 := Measure.restrict_eq_zero.mpr (graphSet_null μ ν hf)
