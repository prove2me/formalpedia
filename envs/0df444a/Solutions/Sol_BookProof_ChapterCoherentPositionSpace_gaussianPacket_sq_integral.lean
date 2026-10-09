-- Prove2me | solution 1 for BookProof.ChapterCoherentPositionSpace.gaussianPacket_sq_integral
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:31:50.411673+00:00
-- url     : https://prove2.me/submissions/a8c89e74-5701-495b-9738-2b7c41a5fd83

-- Generated from ChapterCoherentPositionSpace.lean — solution of BookProof.ChapterCoherentPositionSpace.gaussianPacket_sq_integral
import Mathlib
import Definitions.Def_ChapterCoherentPositionSpace
import Theorems.Thm_BookProof_ChapterCoherentPositionSpace_gaussianPacket_inner
open BookProof.ChapterCoherentPositionSpace



open scoped BigOperators
open MeasureTheory

noncomputable section


open BookProof.ChapterCoherentOverlap BookProof.ChapterSoftmaxSharpness

set_option maxHeartbeats 1000000 in
theorem solution (a : ℝ) :
    (∫ x : ℝ, gaussianPacket a x * gaussianPacket a x) = 1 := by

  rw [gaussianPacket_inner]; simp
