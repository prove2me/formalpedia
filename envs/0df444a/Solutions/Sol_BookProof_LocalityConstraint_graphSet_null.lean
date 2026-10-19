-- Prove2me | solution 1 for BookProof.LocalityConstraint.graphSet_null
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:30:35.015362+00:00
-- url     : https://prove2.me/submissions/99d7e3ab-a240-4716-a7fe-facf4bc27134

import Mathlib
import Definitions.Def_ChapterLocalityConstraintNull
-- Generated from ChapterLocalityConstraintNull.lean — theorem BookProof.LocalityConstraint.graphSet_null
open BookProof.LocalityConstraint



open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {α : Type*} [MeasurableSpace α]
open MeasureTheory in
theorem h44l_null {α : Type*} [MeasurableSpace α] (μ : Measure α) (ν : Measure ℝ) [SFinite ν]
    [NullSingletonClass ν] {f : α → ℝ} (hf : Measurable f) :
    (μ.prod ν) (BookProof.LocalityConstraint.graphSet f) = 0 := by
  have hm : MeasurableSet (BookProof.LocalityConstraint.graphSet f) :=
    measurableSet_eq_fun measurable_snd (hf.comp measurable_fst)
  rw [Measure.prod_apply hm]
  have : ∀ x, Prod.mk x ⁻¹' BookProof.LocalityConstraint.graphSet f = {f x} := by
    intro x; ext y; simp [BookProof.LocalityConstraint.graphSet]
  simp [this]

theorem solution (μ : Measure α) (ν : Measure ℝ) [SFinite ν] [NullSingletonClass ν]
    {f : α → ℝ} (hf : Measurable f) :
    (μ.prod ν) (graphSet f) = 0 := by
  exact h44l_null μ ν hf

