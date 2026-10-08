-- Prove2me | solution 1 for BookProof.ChapterAbelianMixture.mixtureMeasure_atom
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:56:44.062878+00:00
-- url     : https://prove2.me/submissions/a8391c77-1fef-4e96-9df4-63f635a4ea05

-- Generated from ChapterAbelianMixture.lean — theorem BookProof.ChapterAbelianMixture.mixtureMeasure_atom
import Mathlib
import Definitions.Def_ChapterAbelianMixture
open BookProof.ChapterAbelianMixture


noncomputable section

open MeasureTheory ENNReal

namespace BookProof.ChapterAbelianMixture
end BookProof.ChapterAbelianMixture

theorem solution : mixtureMeasure {(2 : ℝ)} = 1 := by
  rw [mixtureMeasure_apply _ (measurableSet_singleton _)]
  simp

#print axioms solution

