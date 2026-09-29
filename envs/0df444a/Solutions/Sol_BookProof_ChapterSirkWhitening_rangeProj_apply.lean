-- Prove2me | solution 1 for BookProof.ChapterSirkWhitening.rangeProj_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T01:41:13.542373+00:00
-- url     : https://prove2.me/submissions/c8976c11-d6df-4334-9cf7-5b1cd61cfdb8

-- Generated from ChapterSirkWhitening.lean — solution of BookProof.ChapterSirkWhitening.rangeProj_apply
import Mathlib
import Definitions.Def_ChapterSirkWhitening
open BookProof.ChapterSirkWhitening








noncomputable section


open BookProof.ChapterH4

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

set_option maxHeartbeats 1000000 in
theorem solution (V : F →L[ℂ] E) (u : E) :
    rangeProj V u = V (V.adjoint u) := rfl
