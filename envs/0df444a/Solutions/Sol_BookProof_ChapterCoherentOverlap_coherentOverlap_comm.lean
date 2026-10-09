-- Prove2me | solution 1 for BookProof.ChapterCoherentOverlap.coherentOverlap_comm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:15:31.429636+00:00
-- url     : https://prove2.me/submissions/b75cfdbf-2ab9-4132-bcfc-7eaf49ec9434

-- Generated from ChapterCoherentOverlap.lean — solution of BookProof.ChapterCoherentOverlap.coherentOverlap_comm
import Mathlib
import Definitions.Def_ChapterCoherentOverlap
open BookProof.ChapterCoherentOverlap



open scoped BigOperators

noncomputable section


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q k : EuclideanSpace ℝ (Fin n)) :
    coherentOverlap q k = coherentOverlap k q := by

  rw [coherentOverlap, coherentOverlap, real_inner_comm]
  ring_nf
