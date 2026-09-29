-- Prove2me | solution 1 for BookProof.ChapterSirkWhitening.rangeProj_isSelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T02:19:46.574826+00:00
-- url     : https://prove2.me/submissions/c82ea3ba-8abc-4f7d-8f5d-1a7c7d5b80f6

-- Generated from ChapterSirkWhitening.lean — solution of BookProof.ChapterSirkWhitening.rangeProj_isSelfAdjoint
import Mathlib
import Definitions.Def_ChapterSirkWhitening
import Theorems.Thm_BookProof_ChapterSirkWhitening_rangeProj_adjoint
open BookProof.ChapterSirkWhitening








noncomputable section


open BookProof.ChapterH4

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

set_option maxHeartbeats 1000000 in
theorem solution (V : F →L[ℂ] E) : IsSelfAdjoint (rangeProj V) := rangeProj_adjoint V
