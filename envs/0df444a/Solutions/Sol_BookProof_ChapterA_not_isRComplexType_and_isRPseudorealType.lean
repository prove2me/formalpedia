-- Prove2me | solution 1 for BookProof.ChapterA.not_isRComplexType_and_isRPseudorealType
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:43:40.795478+00:00
-- url     : https://prove2.me/submissions/3107e153-7862-4d39-a14e-f2f3cb07ab89

-- Generated from ChapterA1h.lean — solution of BookProof.ChapterA.not_isRComplexType_and_isRPseudorealType
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
    ¬ (IsRComplexType M ∧ IsRPseudorealType M) := fun h => h.1.2 h.2
