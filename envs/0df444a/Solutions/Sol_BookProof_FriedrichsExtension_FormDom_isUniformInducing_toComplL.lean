-- Prove2me | solution 1 for BookProof.FriedrichsExtension.FormDom.isUniformInducing_toComplL
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T11:17:51.111248+00:00
-- url     : https://prove2.me/submissions/6c05a8fa-0640-4357-9bae-b4796cd7327b

-- Generated from ChapterFriedrichsExtension.lean — solution of BookProof.FriedrichsExtension.FormDom.isUniformInducing_toComplL
import Mathlib
import Definitions.Def_ChapterFriedrichsExtension
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom




open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.HermiteGalerkin

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution (P : PosSymOp F) :
    IsUniformInducing (UniformSpace.Completion.toComplL (𝕜 := ℂ) (E := FormDom P)) := by

  simpa [UniformSpace.Completion.coe_toComplL] using
    UniformSpace.Completion.isUniformInducing_coe (FormDom P)
