-- Prove2me | solution 1 for BookProof.ChapterA.IsRReal.isRRealType
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:43:44.045391+00:00
-- url     : https://prove2.me/submissions/a88aba94-e453-4c86-8b3f-01fe2373dad6

-- Generated from ChapterA1h.lean — solution of BookProof.ChapterA.IsRReal.isRRealType
import Mathlib
import Definitions.Def_ChapterA1h
import Theorems.Thm_BookProof_ChapterA_IsRReal_not_hasCommutingRImaginary
import Definitions.Def_Complexification
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace


open BookProof.Complexification

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

set_option maxHeartbeats 1000000 in
theorem solution [Nontrivial W] {M : System ℝ W} (h : IsRReal M) :
    IsRRealType M := h.not_hasCommutingRImaginary
