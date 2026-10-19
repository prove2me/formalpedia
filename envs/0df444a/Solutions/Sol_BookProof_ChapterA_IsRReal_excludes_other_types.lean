-- Prove2me | solution 1 for BookProof.ChapterA.IsRReal.excludes_other_types
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:08:29.796355+00:00
-- url     : https://prove2.me/submissions/83284ef0-b4d3-4ed5-940c-cf92f1848442

-- Generated from ChapterA1h.lean — solution of BookProof.ChapterA.IsRReal.excludes_other_types
import Mathlib
import Definitions.Def_ChapterA1h
import Theorems.Thm_BookProof_ChapterA_IsRReal_isRRealType
import Theorems.Thm_BookProof_ChapterA_IsRComplexType_not_isRReal
import Theorems.Thm_BookProof_ChapterA_IsRPseudorealType_not_isRReal
import Definitions.Def_Complexification
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace


open BookProof.Complexification

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

set_option maxHeartbeats 1000000 in
theorem solution [Nontrivial W] {M : System ℝ W}
    (h : IsRReal M) : IsRRealType M ∧ ¬ IsRComplexType M ∧ ¬ IsRPseudorealType M := by

  refine ⟨h.isRRealType, ?_, ?_⟩
  · exact fun hc => hc.not_isRReal h
  · exact fun hc => hc.not_isRReal h
