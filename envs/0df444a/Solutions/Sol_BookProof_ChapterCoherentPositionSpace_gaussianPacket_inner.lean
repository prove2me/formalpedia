-- Prove2me | solution 1 for BookProof.ChapterCoherentPositionSpace.gaussianPacket_inner
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:31:37.048987+00:00
-- url     : https://prove2.me/submissions/6a36bd45-8538-4aac-8a40-a465615d9cda

-- Generated from ChapterCoherentPositionSpace.lean — solution of BookProof.ChapterCoherentPositionSpace.gaussianPacket_inner
import Mathlib
import Definitions.Def_ChapterCoherentPositionSpace
import Theorems.Thm_BookProof_ChapterCoherentPositionSpace_packetNorm_sq
import Theorems.Thm_BookProof_ChapterCoherentPositionSpace_integral_exp_mul_exp
open BookProof.ChapterCoherentPositionSpace



open scoped BigOperators
open MeasureTheory

noncomputable section


open BookProof.ChapterCoherentOverlap BookProof.ChapterSoftmaxSharpness

set_option maxHeartbeats 1000000 in
theorem solution (a b : ℝ) :
    (∫ x : ℝ, gaussianPacket a x * gaussianPacket b x) = Real.exp (-(a - b) ^ 2 / 4) := by

  have hpt : ∀ x : ℝ, gaussianPacket a x * gaussianPacket b x
      = packetNorm ^ 2 * (Real.exp (-(x - a) ^ 2 / 2) * Real.exp (-(x - b) ^ 2 / 2)) := by
    intro x; simp only [gaussianPacket]; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    MeasureTheory.integral_const_mul, integral_exp_mul_exp, packetNorm_sq]
  field_simp
