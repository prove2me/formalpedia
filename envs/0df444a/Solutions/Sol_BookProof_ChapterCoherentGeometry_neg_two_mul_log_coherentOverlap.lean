-- Prove2me | solution 1 for BookProof.ChapterCoherentGeometry.neg_two_mul_log_coherentOverlap
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:10:42.321961+00:00
-- url     : https://prove2.me/submissions/6c5a7b36-aad6-4518-8712-62df1348deeb

-- Generated from ChapterCoherentGeometry.lean — solution of BookProof.ChapterCoherentGeometry.neg_two_mul_log_coherentOverlap
import Mathlib
import Definitions.Def_ChapterCoherentGeometry
import Theorems.Thm_BookProof_ChapterCoherentOverlap_coherentOverlap_eq_gaussian
open BookProof.ChapterCoherentGeometry



open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlap BookProof.ChapterSoftmaxBorn

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q k : EuclideanSpace ℝ (Fin n)) :
    -2 * Real.log (coherentOverlap q k) = ‖q - k‖ ^ 2 := by

  rw [coherentOverlap_eq_gaussian, Real.log_exp]
  ring
