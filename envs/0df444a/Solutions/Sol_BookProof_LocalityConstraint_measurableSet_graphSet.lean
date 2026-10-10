-- Prove2me | solution 1 for BookProof.LocalityConstraint.measurableSet_graphSet
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T13:05:28.616628+00:00
-- url     : https://prove2.me/submissions/119370d1-32d4-4688-8c6e-665f072ea053

import Mathlib
import Definitions.Def_ChapterLocalityConstraintNull
open BookProof.LocalityConstraint
open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {α : Type*} [MeasurableSpace α]

theorem solution {f : α → ℝ} (hf : Measurable f) : MeasurableSet (graphSet f) := by
  unfold graphSet
  simpa using measurableSet_eq_fun measurable_snd (hf.comp measurable_fst)
