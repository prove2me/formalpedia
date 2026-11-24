-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd10.Ps_free
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:54:26.923873+00:00
-- url     : https://prove2.me/submissions/15dae999-82f7-4390-99bc-822eb81012e5

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferMatrixFactorization
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PartialFlipCommuteDiagScalarOfFree
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_free_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_free_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_freeOf_J_matrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_freeOf2_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_freeOf_matrix_transpose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_freeOf_matrix_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_freeOf_matrix_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_freeOf2_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd5_freeOf2_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd5_free_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd5_free_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_freeOf2_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_freeOf_J_matrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_freeOf_matrix_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_freeOf_matrix_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_free_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd10
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd10
theorem _root_.solution (hIF : InsFree) (hWF : WordFree) (QQ : K → M2 A) (q : K → K) (w : List (Letter K S))
    (c : S) : ∀ L : List (Letter K S), c ∉ (L ++ w).map Letter.intersection_update_fsHerm_neg_one → FreeOf c (Ps QQ q w L)
  | [], _ => free_one c
  | l :: L, h => by
    rw [List.cons_append, List.map_cons, List.mem_cons, not_or] at h
    have hT := (hWF K A S QQ (L ++ w) c h.2).2
    rw [Ps]
    refine free_mul ?_ (solution hIF hWF QQ q w c L h.2)
    split
    · exact (hIF K A S l.intersection_update_fsHerm_neg_one _).1 c h.1
        (freeOf_matrix_neg (freeOf_matrix_smul _ (freeOf2_mul (freeOf_J_matrix c) (freeOf_matrix_transpose (hT _)))))
    · exact (hIF K A S l.intersection_update_fsHerm_neg_one _).1 c h.1 (freeOf_matrix_smul _ (freeOf2_mul (freeOf_J_matrix c) (hT _)))
end Formalism.FourierDecayAlt.P.Wd10
