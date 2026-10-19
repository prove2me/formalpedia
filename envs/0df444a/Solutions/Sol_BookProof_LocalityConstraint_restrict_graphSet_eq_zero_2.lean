-- Prove2me | solution 2 for BookProof.LocalityConstraint.restrict_graphSet_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:30:45.664289+00:00
-- url     : https://prove2.me/submissions/7d09c7b8-6d9b-4045-8019-790988463d71

import Mathlib
import Definitions.Def_ChapterLocalityConstraintNull
-- Generated from ChapterLocalityConstraintNull.lean — theorem BookProof.LocalityConstraint.restrict_graphSet_eq_zero
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
    (μ.prod ν).restrict (graphSet f) = 0 := by
  exact Measure.restrict_eq_zero.mpr (h44l_null μ ν hf)

