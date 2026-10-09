-- Prove2me | solution 1 for BookProof.ChapterCoherentPositionSpace.gaussianPacket_inner_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:32:05.492935+00:00
-- url     : https://prove2.me/submissions/ceca6b80-cfea-4111-bd4d-2a287be9020c

-- Generated from ChapterCoherentPositionSpace.lean — solution of BookProof.ChapterCoherentPositionSpace.gaussianPacket_inner_eq_one_iff
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
    (∫ x : ℝ, gaussianPacket a x * gaussianPacket b x) = 1 ↔ a = b := by

  rw [gaussianPacket_inner, Real.exp_eq_one_iff]
  constructor
  · intro h
    have : (a - b) ^ 2 = 0 := by linarith
    have := pow_eq_zero_iff (n := 2) two_ne_zero |>.1 this
    linarith
  · rintro rfl; ring
