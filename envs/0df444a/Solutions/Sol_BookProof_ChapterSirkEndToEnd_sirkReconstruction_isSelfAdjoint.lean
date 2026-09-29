-- Prove2me | solution 1 for BookProof.ChapterSirkEndToEnd.sirkReconstruction_isSelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T01:34:59.641122+00:00
-- url     : https://prove2.me/submissions/3ed395f7-9ad3-40f3-bc26-ee4826889f4d

-- Generated from ChapterSirkEndToEnd.lean — solution of BookProof.ChapterSirkEndToEnd.sirkReconstruction_isSelfAdjoint
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
theorem solution (V : F →L[ℂ] E) :
    IsSelfAdjoint (sirkReconstruction V) := by

  change ContinuousLinearMap.adjoint (V.comp V.adjoint) = V.comp V.adjoint
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
