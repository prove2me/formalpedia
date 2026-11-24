-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd4.form_herm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:02:11.844682+00:00
-- url     : https://prove2.me/submissions/22375950-4baa-483e-8278-d3b374054fe5

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_freeOf_diagScalar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_freeOf2_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_insert_diagonal_extract
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd3_ins_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd4
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.W
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd4
theorem _root_.solution {a : S} {RR : SlopeTestRemainingChoices S A} {T : M2 (SlopeTestRemainingChoices S A)} (hRR : FreeOf a RR) (hT : FreeOf2 a T)
    (h : (d0 RR * T)ᴴ = d0 RR * T) : star (RR * ins a T) = RR * ins a T := by
  have h1 : RR * ins a T = ins a (d0 RR * T) := by
    rw [Wd1.ins_mul a _ _ (freeOf_diagScalar hRR), Wd1.insert_diagonal_extract]
  rw [h1, Wd1.ins_star a _ (freeOf2_mul (freeOf_diagScalar hRR) hT), h]
end Formalism.FourierDecayAlt.P.Wd4
