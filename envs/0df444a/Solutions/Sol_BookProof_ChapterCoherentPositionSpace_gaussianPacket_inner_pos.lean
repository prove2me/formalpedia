-- Prove2me | solution 1 for BookProof.ChapterCoherentPositionSpace.gaussianPacket_inner_pos
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:31:51.597477+00:00
-- url     : https://prove2.me/submissions/7eea909a-37e5-4425-b604-37cd213e7aa1

-- Generated from ChapterCoherentPositionSpace.lean — solution of BookProof.ChapterCoherentPositionSpace.gaussianPacket_inner_pos
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
    0 < ∫ x : ℝ, gaussianPacket a x * gaussianPacket b x := by

  rw [gaussianPacket_inner]; exact Real.exp_pos _
