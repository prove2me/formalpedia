-- Prove2me | solution 1 for BookProof.ChapterCoherentPositionSpace.gaussianPacket_inner_le_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:31:52.59173+00:00
-- url     : https://prove2.me/submissions/751ddf32-b647-4b2f-b010-b230231f37a5

-- Generated from ChapterCoherentPositionSpace.lean — solution of BookProof.ChapterCoherentPositionSpace.gaussianPacket_inner_le_one
import Mathlib
import Definitions.Def_ChapterCoherentPositionSpace
import Theorems.Thm_BookProof_ChapterCoherentPositionSpace_gaussianPacket_inner
open BookProof.ChapterCoherentPositionSpace



open scoped BigOperators
open MeasureTheory

noncomputable section


open BookProof.ChapterCoherentOverlap BookProof.ChapterSoftmaxSharpness

set_option maxHeartbeats 1000000 in
theorem solution (a b : ℝ) :
    (∫ x : ℝ, gaussianPacket a x * gaussianPacket b x) ≤ 1 := by

  rw [gaussianPacket_inner, Real.exp_le_one_iff]
  nlinarith [sq_nonneg (a - b)]
