-- Prove2me | solution 1 for BookProof.ChapterCoherentOverlap.inner_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:14:34.925591+00:00
-- url     : https://prove2.me/submissions/1b002af4-d41a-4649-9529-fbafd9d75c3a

-- Generated from ChapterCoherentOverlap.lean — solution of BookProof.ChapterCoherentOverlap.inner_eq_sum
import Mathlib
import Definitions.Def_ChapterCoherentOverlap
open BookProof.ChapterCoherentOverlap



open scoped BigOperators

noncomputable section


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q k : EuclideanSpace ℝ (Fin n)) :
    inner ℝ q k = ∑ i, q i * k i := by

  rw [PiLp.inner_apply]
  simp [mul_comm]
