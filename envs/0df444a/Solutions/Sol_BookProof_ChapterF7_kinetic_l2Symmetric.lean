-- Prove2me | solution 1 for BookProof.ChapterF7.kinetic_l2Symmetric
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:09:16.766121+00:00
-- url     : https://prove2.me/submissions/e315612f-6a96-4a49-8541-6fd0624d8491
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterF7.lean — solution of BookProof.ChapterF7.kinetic_l2Symmetric
import Mathlib
import Definitions.Def_ChapterF7
import Theorems.Thm_BookProof_ChapterF7_momentum_l2Symmetric
import Theorems.Thm_BookProof_ChapterF7_smul_l2Symmetric
open BookProof.ChapterF7



open SchwartzMap MeasureTheory Complex
open scoped BigOperators


noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution : IsL2Symmetric kinetic := by

  refine smul_l2Symmetric (by simp only [map_div₀, map_one, map_ofNat]) ?_
  intro f g
  simp only [ContinuousLinearMap.comp_apply]
  rw [momentum_l2Symmetric, momentum_l2Symmetric]
