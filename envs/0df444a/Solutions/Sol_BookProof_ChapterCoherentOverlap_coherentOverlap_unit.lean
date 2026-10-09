-- Prove2me | solution 1 for BookProof.ChapterCoherentOverlap.coherentOverlap_unit
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:15:33.50882+00:00
-- url     : https://prove2.me/submissions/d0bd3295-ce2e-4dc2-a5df-12a327ad918f

-- Generated from ChapterCoherentOverlap.lean — solution of BookProof.ChapterCoherentOverlap.coherentOverlap_unit
import Mathlib
import Definitions.Def_ChapterCoherentOverlap
import Theorems.Thm_BookProof_ChapterCoherentOverlap_coherentOverlap_self
open BookProof.ChapterCoherentOverlap



open scoped BigOperators

noncomputable section


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q : EuclideanSpace ℝ (Fin n)) (_hq : ‖q‖ = 1) :
    coherentOverlap q q = 1 := coherentOverlap_self q
