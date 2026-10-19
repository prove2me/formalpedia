-- Prove2me | solution 1 for BookProof.ChapterA.rType_exhaustive
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:28:17.106976+00:00
-- url     : https://prove2.me/submissions/ec43972b-f012-495f-9efd-359f84464447

-- Generated from ChapterA1h.lean — solution of BookProof.ChapterA.rType_exhaustive
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
    IsRRealType M ∨ IsRComplexType M ∨ IsRPseudorealType M := by

  by_cases h1 : HasCommutingRImaginary M
  · by_cases h2 : HasQuaternionicRImaginary M
    · exact Or.inr (Or.inr h2)
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
  · exact Or.inl h1
