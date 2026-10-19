-- Prove2me | solution 2 for BookProof.LocalityConstraint.graphSet_volume_null
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:31:15.696699+00:00
-- url     : https://prove2.me/submissions/6c19e788-4165-4b87-ac8d-1caa5f0226d2

import Mathlib
import Definitions.Def_ChapterLocalityConstraintNull
-- Generated from ChapterLocalityConstraintNull.lean — theorem BookProof.LocalityConstraint.graphSet_volume_null
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

theorem solution {f : ℝ → ℝ} (hf : Measurable f) :
    (volume : Measure (ℝ × ℝ)) (graphSet f) = 0 := by
  rw [Measure.volume_eq_prod]
  exact h44l_null volume volume hf

