-- Prove2me | solution 1 for BookProof.ChapterAbelianMixture.mixtureMeasure_not_atomless
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:56:46.046339+00:00
-- url     : https://prove2.me/submissions/eedcf01a-ec58-4d50-9e6c-7dc727feca88

-- Generated from ChapterAbelianMixture.lean — theorem BookProof.ChapterAbelianMixture.mixtureMeasure_not_atomless
import Mathlib
import Definitions.Def_ChapterAbelianMixture
open BookProof.ChapterAbelianMixture


noncomputable section

open MeasureTheory ENNReal

namespace BookProof.ChapterAbelianMixture
theorem mixtureMeasure_atom : mixtureMeasure {(2 : ℝ)} = 1 := by
  rw [mixtureMeasure_apply _ (measurableSet_singleton _)]
  simp
end BookProof.ChapterAbelianMixture

theorem solution : mixtureMeasure {(2 : ℝ)} ≠ 0 := by
  rw [mixtureMeasure_atom]; exact one_ne_zero

#print axioms solution

