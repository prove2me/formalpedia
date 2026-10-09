-- Prove2me | solution 1 for BookProof.ChapterCoherentOverlap.coherentOverlap_self
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:15:32.474457+00:00
-- url     : https://prove2.me/submissions/7c413b90-6385-4638-9d93-557de7f4ff33

-- Generated from ChapterCoherentOverlap.lean — solution of BookProof.ChapterCoherentOverlap.coherentOverlap_self
import Mathlib
import Definitions.Def_ChapterCoherentOverlap
import Theorems.Thm_BookProof_ChapterCoherentOverlap_coherentOverlap_eq_gaussian
open BookProof.ChapterCoherentOverlap



open scoped BigOperators

noncomputable section


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q : EuclideanSpace ℝ (Fin n)) :
    coherentOverlap q q = 1 := by

  rw [coherentOverlap_eq_gaussian]
  simp
