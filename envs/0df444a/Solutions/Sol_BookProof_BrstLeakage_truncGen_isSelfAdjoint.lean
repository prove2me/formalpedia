-- Prove2me | solution 1 for BookProof.BrstLeakage.truncGen_isSelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:46:13.231662+00:00
-- url     : https://prove2.me/submissions/89e03c3e-205c-43e4-8c8d-2063fa7d06e3

-- Generated from ChapterBrstTruncationLeakage.lean — solution of BookProof.BrstLeakage.truncGen_isSelfAdjoint
import Mathlib
import Definitions.Def_ChapterBrstTruncationLeakage
open BookProof.BrstLeakage



open NormedSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution {P H : E →L[ℂ] E} (hP : IsSelfAdjoint P)
    (hH : IsSelfAdjoint H) : IsSelfAdjoint (truncGen P H) := by

  have : star (P * H * P) = P * H * P := by
    rw [star_mul, star_mul, hP.star_eq, hH.star_eq]
    rw [mul_assoc]
  exact this
