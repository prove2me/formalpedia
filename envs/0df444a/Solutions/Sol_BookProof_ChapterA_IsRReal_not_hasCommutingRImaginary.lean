-- Prove2me | solution 1 for BookProof.ChapterA.IsRReal.not_hasCommutingRImaginary
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:43:43.038679+00:00
-- url     : https://prove2.me/submissions/6530a6c0-73b0-411c-abd1-8792c7cbba27

-- Generated from ChapterA1h.lean — solution of BookProof.ChapterA.IsRReal.not_hasCommutingRImaginary
import Mathlib
import Definitions.Def_ChapterA1h
import Theorems.Thm_BookProof_ChapterA_cxSystem_reducible_of_commuting_rImaginary
import Definitions.Def_Complexification
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace


open BookProof.Complexification

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

set_option maxHeartbeats 1000000 in
theorem solution [Nontrivial W] {M : System ℝ W}
    (h : IsRReal M) : ¬ HasCommutingRImaginary M := fun hJ => cxSystem_reducible_of_commuting_rImaginary M hJ h
