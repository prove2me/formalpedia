-- Prove2me | solution 1 for BookProof.ChapterSirkTruncation.compress_comp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T07:21:56.875894+00:00
-- url     : https://prove2.me/submissions/024b0de2-4fe3-49dd-91ba-1073b7812d1b

-- Generated from ChapterSirkTruncation.lean — solution of BookProof.ChapterSirkTruncation.compress_comp
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
theorem solution (V : F →L[ℂ] E) (W : G →L[ℂ] F) (X : E →L[ℂ] E) :
    compress (V.comp W) X = compress W (compress V X) := by

  simp [compress, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc]
