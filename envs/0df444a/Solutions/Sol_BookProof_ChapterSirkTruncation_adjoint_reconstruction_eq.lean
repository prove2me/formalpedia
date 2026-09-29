-- Prove2me | solution 1 for BookProof.ChapterSirkTruncation.adjoint_reconstruction_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T07:20:26.704684+00:00
-- url     : https://prove2.me/submissions/38f04005-ce52-45c0-bd77-f110f0132f60

-- Generated from ChapterSirkTruncation.lean — solution of BookProof.ChapterSirkTruncation.adjoint_reconstruction_eq
import Mathlib
import Definitions.Def_ChapterSirkTruncation
open BookProof.ChapterSirkTruncation









noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterSirkEndToEnd
open BookProof.ChapterSirkWhitening

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

set_option maxHeartbeats 1000000 in
theorem solution (V : F →L[ℂ] E)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F) (v : E) :
    V.adjoint (V (V.adjoint v)) = V.adjoint v := congrArg (fun f : F →L[ℂ] F => f (V.adjoint v)) hVV
