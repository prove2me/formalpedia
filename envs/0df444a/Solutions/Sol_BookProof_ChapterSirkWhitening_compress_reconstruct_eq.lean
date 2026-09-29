-- Prove2me | solution 1 for BookProof.ChapterSirkWhitening.compress_reconstruct_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T01:36:44.032403+00:00
-- url     : https://prove2.me/submissions/6862afb7-56f0-4866-bad9-09dad6b1145b

-- Generated from ChapterSirkWhitening.lean — solution of BookProof.ChapterSirkWhitening.compress_reconstruct_eq
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
theorem solution (V : F →L[ℂ] E) (X : E →L[ℂ] E) :
    V.comp ((compress V X).comp V.adjoint) = (rangeProj V).comp (X.comp (rangeProj V)) := by

  ext u
  simp [compress, rangeProj]
