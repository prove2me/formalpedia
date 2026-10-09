-- Prove2me | solution 1 for BookProof.ChapterCoherentOverlap.coherentOverlap_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:15:29.266533+00:00
-- url     : https://prove2.me/submissions/9343c1a5-91b0-4930-ad9a-bff877c133ae

-- Generated from ChapterCoherentOverlap.lean — solution of BookProof.ChapterCoherentOverlap.coherentOverlap_ne_zero
import Mathlib
import Definitions.Def_ChapterCoherentOverlap
import Theorems.Thm_BookProof_ChapterCoherentOverlap_coherentOverlap_pos
open BookProof.ChapterCoherentOverlap



open scoped BigOperators

noncomputable section


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q k : EuclideanSpace ℝ (Fin n)) :
    coherentOverlap q k ≠ 0 := ne_of_gt (coherentOverlap_pos q k)
