-- Prove2me | solution 1 for BookProof.ChapterCoherentOverlap.norm_sq_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:14:09.563565+00:00
-- url     : https://prove2.me/submissions/ef82ed5a-fbe7-4d7e-9035-b1285289e8bc

-- Generated from ChapterCoherentOverlap.lean — solution of BookProof.ChapterCoherentOverlap.norm_sq_eq_sum
import Mathlib
import Definitions.Def_ChapterCoherentOverlap
open BookProof.ChapterCoherentOverlap



open scoped BigOperators

noncomputable section


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q : EuclideanSpace ℝ (Fin n)) :
    ‖q‖ ^ 2 = ∑ i, q i * q i := by

  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  simp [sq]
