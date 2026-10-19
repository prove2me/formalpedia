-- Prove2me | solution 1 for BookProof.FriedrichsCanonical.resolvent_mem_friedrichsDomain
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-18T10:31:30.17229+00:00
-- url     : https://prove2.me/submissions/b613da87-7a66-4080-a390-a3ec626228c6

-- Generated from ChapterFriedrichsCanonical.lean — solution of BookProof.FriedrichsCanonical.resolvent_mem_friedrichsDomain
import Mathlib
import Definitions.Def_ChapterFriedrichsCanonical
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterFriedrichsExtension
open BookProof.FriedrichsCanonical




open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (P : PosSymOp F) (u : F) :
    friedrichsResolvent P u ∈ friedrichsDomain P := ⟨u, rfl⟩
