-- Prove2me | solution 1 for BookProof.ChapterA.not_isRRealType_and_isRPseudorealType
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:08:26.243503+00:00
-- url     : https://prove2.me/submissions/1c5bb476-bbf8-4970-9a11-f30aab1fc3b7

-- Generated from ChapterA1h.lean — solution of BookProof.ChapterA.not_isRRealType_and_isRPseudorealType
import Mathlib
import Definitions.Def_ChapterA1h
import Theorems.Thm_BookProof_ChapterA_HasQuaternionicRImaginary_hasCommutingRImaginary
import Definitions.Def_Complexification
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace


open BookProof.Complexification

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

set_option maxHeartbeats 1000000 in
theorem solution (M : System ℝ W) :
    ¬ (IsRRealType M ∧ IsRPseudorealType M) := fun h => h.1 h.2.hasCommutingRImaginary
