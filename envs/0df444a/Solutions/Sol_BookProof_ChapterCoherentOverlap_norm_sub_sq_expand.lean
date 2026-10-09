-- Prove2me | solution 1 for BookProof.ChapterCoherentOverlap.norm_sub_sq_expand
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:14:35.875973+00:00
-- url     : https://prove2.me/submissions/938c042b-0825-4796-a063-6feccfb13b1c

-- Generated from ChapterCoherentOverlap.lean — solution of BookProof.ChapterCoherentOverlap.norm_sub_sq_expand
import Mathlib
import Definitions.Def_ChapterCoherentOverlap
open BookProof.ChapterCoherentOverlap



open scoped BigOperators

noncomputable section


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q k : EuclideanSpace ℝ (Fin n)) :
    ‖q - k‖ ^ 2 = ‖q‖ ^ 2 + ‖k‖ ^ 2 - 2 * inner ℝ q k := by

  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq, inner_sub_sub_self]
  ring_nf
  rw [real_inner_comm k q]
  ring
