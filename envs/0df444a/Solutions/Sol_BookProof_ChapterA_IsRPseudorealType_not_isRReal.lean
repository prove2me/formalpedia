-- Prove2me | solution 1 for BookProof.ChapterA.IsRPseudorealType.not_isRReal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:43:46.270991+00:00
-- url     : https://prove2.me/submissions/b2eafa4f-bfc9-44a4-a964-5c43b93fcd15

-- Generated from ChapterA1h.lean — solution of BookProof.ChapterA.IsRPseudorealType.not_isRReal
import Mathlib
import Definitions.Def_ChapterA1h
import Theorems.Thm_BookProof_ChapterA_HasQuaternionicRImaginary_hasCommutingRImaginary
import Theorems.Thm_BookProof_ChapterA_IsRReal_not_hasCommutingRImaginary
import Definitions.Def_Complexification
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace


open BookProof.Complexification

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

set_option maxHeartbeats 1000000 in
theorem solution [Nontrivial W] {M : System ℝ W}
    (h : IsRPseudorealType M) : ¬ IsRReal M := fun hRReal => hRReal.not_hasCommutingRImaginary h.hasCommutingRImaginary
