-- Prove2me | solution 1 for BookProof.ChapterCoherentPositionSpace.gaussianPacket_inner_sq_eq_coherentOverlap
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:32:18.992089+00:00
-- url     : https://prove2.me/submissions/c2a07856-31d0-4357-94ce-d3ec432bd686

-- Generated from ChapterCoherentPositionSpace.lean — solution of BookProof.ChapterCoherentPositionSpace.gaussianPacket_inner_sq_eq_coherentOverlap
import Mathlib
import Definitions.Def_ChapterCoherentPositionSpace
import Theorems.Thm_BookProof_ChapterCoherentPositionSpace_gaussianPacket_inner
import Theorems.Thm_BookProof_ChapterCoherentOverlap_inner_eq_sum
import Theorems.Thm_BookProof_ChapterCoherentOverlap_norm_sq_eq_sum
open BookProof.ChapterCoherentPositionSpace



open scoped BigOperators
open MeasureTheory

noncomputable section


open BookProof.ChapterCoherentOverlap BookProof.ChapterSoftmaxSharpness

set_option maxHeartbeats 1000000 in
theorem solution (a b : ℝ) :
    (∫ x : ℝ, gaussianPacket a x * gaussianPacket b x) ^ 2
      = coherentOverlap (WithLp.toLp 2 (fun _ => a) : EuclideanSpace ℝ (Fin 1))
          (WithLp.toLp 2 (fun _ => b)) := by

  have hq : ‖(WithLp.toLp 2 (fun _ => a) : EuclideanSpace ℝ (Fin 1))‖ ^ 2 = a * a := by
    rw [norm_sq_eq_sum]; simp
  have hk : ‖(WithLp.toLp 2 (fun _ => b) : EuclideanSpace ℝ (Fin 1))‖ ^ 2 = b * b := by
    rw [norm_sq_eq_sum]; simp
  have hin : (inner ℝ (WithLp.toLp 2 (fun _ => a) : EuclideanSpace ℝ (Fin 1))
      (WithLp.toLp 2 (fun _ => b) : EuclideanSpace ℝ (Fin 1)) : ℝ) = a * b := by
    rw [inner_eq_sum]; simp
  rw [gaussianPacket_inner, ← Real.exp_nat_mul, coherentOverlap, hq, hk, hin]
  ring_nf
