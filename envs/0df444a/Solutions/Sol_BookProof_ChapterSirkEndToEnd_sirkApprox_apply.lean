-- Prove2me | solution 1 for BookProof.ChapterSirkEndToEnd.sirkApprox_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T01:30:29.035619+00:00
-- url     : https://prove2.me/submissions/541ba65e-9600-4696-a29e-58e3bde2c5ea

-- Generated from ChapterSirkEndToEnd.lean — solution of BookProof.ChapterSirkEndToEnd.sirkApprox_apply
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
theorem solution (V : F →L[ℂ] E) (psiB : F →L[ℂ] F) (v : E) :
    sirkApprox V psiB v = V (psiB (V.adjoint v)) := rfl
