-- Prove2me | solution 1 for BookProof.ChapterSirkWhitening.rangeProj_comp_embedding
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T01:42:43.885437+00:00
-- url     : https://prove2.me/submissions/70e42db5-a925-4271-adf0-39fcaf266670

-- Generated from ChapterSirkWhitening.lean — solution of BookProof.ChapterSirkWhitening.rangeProj_comp_embedding
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
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F) (y : F) :
    rangeProj V (V y) = V y := by

  have h : V.adjoint (V y) = y := congrArg (fun f : F →L[ℂ] F => f y) hVV
  simp [rangeProj, h]
