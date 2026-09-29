-- Prove2me | solution 1 for BookProof.FriedrichsExtension.FormDom.incl_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T11:17:50.059066+00:00
-- url     : https://prove2.me/submissions/0e44089f-3f79-49e1-abe0-624fbcba00b4

-- Generated from ChapterFriedrichsExtension.lean — solution of BookProof.FriedrichsExtension.FormDom.incl_apply
import Mathlib
import Definitions.Def_ChapterFriedrichsExtension
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom




open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.HermiteGalerkin

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution {P : PosSymOp F} (x : FormDom P) : incl P x = toAmbient x := rfl
