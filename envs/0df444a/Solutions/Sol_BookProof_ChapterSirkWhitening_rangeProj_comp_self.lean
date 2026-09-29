-- Prove2me | solution 1 for BookProof.ChapterSirkWhitening.rangeProj_comp_self
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T01:44:24.068509+00:00
-- url     : https://prove2.me/submissions/b1091352-3428-41ed-8e02-1c4b5639709b

-- Generated from ChapterSirkWhitening.lean — solution of BookProof.ChapterSirkWhitening.rangeProj_comp_self
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
theorem solution (V : F →L[ℂ] E)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F) :
    (rangeProj V).comp (rangeProj V) = rangeProj V := by

  ext u
  have h : V.adjoint (V (V.adjoint u)) = V.adjoint u :=
    congrArg (fun f : F →L[ℂ] F => f (V.adjoint u)) hVV
  simp [rangeProj, h]
