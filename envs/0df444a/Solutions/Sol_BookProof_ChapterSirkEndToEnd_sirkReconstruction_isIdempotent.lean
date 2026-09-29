-- Prove2me | solution 1 for BookProof.ChapterSirkEndToEnd.sirkReconstruction_isIdempotent
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T01:33:08.351227+00:00
-- url     : https://prove2.me/submissions/ef047ada-c8b6-4c21-bb64-2b5ce2ffc9d3

-- Generated from ChapterSirkEndToEnd.lean — solution of BookProof.ChapterSirkEndToEnd.sirkReconstruction_isIdempotent
import Mathlib
import Definitions.Def_ChapterSirkEndToEnd
open BookProof.ChapterSirkEndToEnd











noncomputable section

open Filter Topology


open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterH8 BookProof.ChapterH9

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (V : F →L[ℂ] E)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F) :
    (sirkReconstruction V).comp (sirkReconstruction V) = sirkReconstruction V := by

  ext v
  have h : V.adjoint (V (V.adjoint v)) = V.adjoint v :=
    congrArg (fun f : F →L[ℂ] F => f (V.adjoint v)) hVV
  simp [sirkReconstruction, h]
