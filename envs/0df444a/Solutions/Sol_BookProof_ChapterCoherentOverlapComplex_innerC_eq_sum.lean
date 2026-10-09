-- Prove2me | solution 1 for BookProof.ChapterCoherentOverlapComplex.innerC_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:27:13.390399+00:00
-- url     : https://prove2.me/submissions/67764333-cf65-4060-8748-90af407d0a32

-- Generated from ChapterCoherentOverlapComplex.lean — solution of BookProof.ChapterCoherentOverlapComplex.innerC_eq_sum
import Mathlib
import Definitions.Def_ChapterCoherentOverlapComplex
open BookProof.ChapterCoherentOverlapComplex



open scoped BigOperators

noncomputable section


variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q k : EuclideanSpace ℂ (Fin n)) :
    inner ℂ q k = ∑ i, (starRingEnd ℂ) (q i) * k i := by

  rw [PiLp.inner_apply]
  simp [RCLike.inner_apply, mul_comm]
