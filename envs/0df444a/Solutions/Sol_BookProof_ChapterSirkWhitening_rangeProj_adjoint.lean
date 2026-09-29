-- Prove2me | solution 1 for BookProof.ChapterSirkWhitening.rangeProj_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T01:39:33.423658+00:00
-- url     : https://prove2.me/submissions/a25171a1-2673-4831-974e-5f2d619c8645

-- Generated from ChapterSirkWhitening.lean — solution of BookProof.ChapterSirkWhitening.rangeProj_adjoint
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
theorem solution (V : F →L[ℂ] E) :
    ContinuousLinearMap.adjoint (rangeProj V) = rangeProj V := by

  rw [rangeProj, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
