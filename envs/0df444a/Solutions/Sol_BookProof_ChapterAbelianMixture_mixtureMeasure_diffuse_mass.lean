-- Prove2me | solution 1 for BookProof.ChapterAbelianMixture.mixtureMeasure_diffuse_mass
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:56:47.735389+00:00
-- url     : https://prove2.me/submissions/9b69d998-a42b-40cc-bbca-247486945de4

-- Generated from ChapterAbelianMixture.lean — theorem BookProof.ChapterAbelianMixture.mixtureMeasure_diffuse_mass
import Mathlib
import Definitions.Def_ChapterAbelianMixture
open BookProof.ChapterAbelianMixture


noncomputable section

open MeasureTheory ENNReal

namespace BookProof.ChapterAbelianMixture
end BookProof.ChapterAbelianMixture

theorem solution : mixtureMeasure (Set.Icc (0 : ℝ) 1) = 1 := by
  rw [mixtureMeasure_apply _ measurableSet_Icc]
  have h2 : ((2 : ℝ)) ∉ Set.Icc (0 : ℝ) 1 := by norm_num
  simp [Real.volume_Icc, Measure.dirac_apply' _ measurableSet_Icc, h2]

#print axioms solution

