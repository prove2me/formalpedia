-- Prove2me | solution 1 for BookProof.ChapterCoherentOverlap.coherentOverlap_eq_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:15:02.041992+00:00
-- url     : https://prove2.me/submissions/a9606a31-05af-4fa7-aafa-1c8c8c551a86

-- Generated from ChapterCoherentOverlap.lean — solution of BookProof.ChapterCoherentOverlap.coherentOverlap_eq_gaussian
import Mathlib
import Definitions.Def_ChapterCoherentOverlap
import Theorems.Thm_BookProof_ChapterCoherentOverlap_norm_sub_sq_expand
open BookProof.ChapterCoherentOverlap



open scoped BigOperators

noncomputable section


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q k : EuclideanSpace ℝ (Fin n)) :
    coherentOverlap q k = Real.exp (-‖q - k‖ ^ 2 / 2) := by

  rw [coherentOverlap, norm_sub_sq_expand]
  ring_nf
