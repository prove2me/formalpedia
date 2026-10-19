-- Prove2me | solution 1 for BookProof.FriedrichsCanonical.eq_zero_of_inner_coe_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-19T05:39:45.476081+00:00
-- url     : https://prove2.me/submissions/9367a8e8-7af3-4730-85d2-535b1211b3a3

-- Generated from ChapterFriedrichsCanonical.lean — solution of BookProof.FriedrichsCanonical.eq_zero_of_inner_coe_eq_zero
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
open BookProof.FriedrichsExtension BookProof.FriedrichsExtension

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (P : PosSymOp F) (k : FormSpace P)
    (h : ∀ v : FormDom P, (inner ℂ (v : FormSpace P) k : ℂ) = 0) : k = 0 := by

  have hall : ∀ z : FormSpace P, (inner ℂ z k : ℂ) = 0 := by
    intro z
    refine UniformSpace.Completion.induction_on z ?_ h
    exact isClosed_eq (by fun_prop) (by fun_prop)
  simpa using hall k
