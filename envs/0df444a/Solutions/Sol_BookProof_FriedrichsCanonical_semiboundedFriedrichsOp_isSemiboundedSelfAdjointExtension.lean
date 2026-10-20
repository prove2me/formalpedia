-- Prove2me | solution 1 for BookProof.FriedrichsCanonical.semiboundedFriedrichsOp_isSemiboundedSelfAdjointExtension
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-19T14:35:57.74689+00:00
-- url     : https://prove2.me/submissions/6a68fcc9-b9eb-44c9-a994-5a77cc8fb434

-- Generated from ChapterFriedrichsCanonical.lean — solution of BookProof.FriedrichsCanonical.semiboundedFriedrichsOp_isSemiboundedSelfAdjointExtension
import Mathlib
import Definitions.Def_ChapterFriedrichsCanonical
import Theorems.Thm_BookProof_FriedrichsCanonical_friedrichsOp_isPositiveSelfAdjointExtension
import Theorems.Thm_BookProof_FriedrichsCanonical_isSemibounded_of_isPositive_shift
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFriedrichsExtension
open BookProof.FriedrichsCanonical




open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {D : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution (H : D →ₗ[ℂ] F)
    (hsym : SymmetricOn D H) (c : ℝ)
    (hbelow : ∀ x : D, -c * ‖(x : F)‖ ^ 2 ≤ quadForm H x) (hdense : Dense (D : Set F)) :
    IsSemiboundedSelfAdjointExtension c H (semiboundedFriedrichsOp H hsym c hbelow hdense) :=
  isSemibounded_of_isPositive_shift H c _
      (friedrichsOp_isPositiveSelfAdjointExtension (shiftedPosSymOp H hsym c hbelow) hdense)
