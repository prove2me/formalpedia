-- Prove2me | solution 1 for BookProof.ChapterA.not_isRRealType_and_isRComplexType
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:28:18.284498+00:00
-- url     : https://prove2.me/submissions/ab508c09-525c-486c-9d64-0a3273709dd4

-- Generated from ChapterA1h.lean — solution of BookProof.ChapterA.not_isRRealType_and_isRComplexType
import Mathlib
import Definitions.Def_ChapterA1h
import Definitions.Def_Complexification
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace


open BookProof.Complexification

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

set_option maxHeartbeats 1000000 in
theorem solution (M : System ℝ W) :
    ¬ (IsRRealType M ∧ IsRComplexType M) := fun h => h.1 h.2.1
