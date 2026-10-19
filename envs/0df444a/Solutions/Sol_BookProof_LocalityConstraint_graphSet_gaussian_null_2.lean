-- Prove2me | solution 2 for BookProof.LocalityConstraint.graphSet_gaussian_null
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:31:34.753745+00:00
-- url     : https://prove2.me/submissions/be18b86c-9160-4593-bee0-0729f89b65fb

import Mathlib
import Definitions.Def_ChapterLocalityConstraintNull
-- Generated from ChapterLocalityConstraintNull.lean — theorem BookProof.LocalityConstraint.graphSet_gaussian_null
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

theorem solution (m₁ m₂ : ℝ) (v₁ : ℝ≥0) (v₂ : ℝ≥0) (hv₂ : v₂ ≠ 0)
    {f : ℝ → ℝ} (hf : Measurable f) :
    ((gaussianReal m₁ v₁).prod (gaussianReal m₂ v₂)) (graphSet f) = 0 := by
  haveI := ProbabilityTheory.nullSingletonClass_gaussianReal (μ := m₂) hv₂
  exact h44l_null _ _ hf

