-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd11.freeOf_transfer_word_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:42:47.809526+00:00
-- url     : https://prove2.me/submissions/b5ebe890-6351-4c6e-9575-d20ada8edfdd

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_freeOf2_lift
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_freeOf2_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_freeOf2_rmatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_freeOf2_rmatrix_transpose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd11
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.Wd1
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd11
theorem _root_.solution (QQ : K → M2 A) (w : List (Letter K S)) (c : S)
    (hc : c ∉ w.map Letter.intersection_update_fsHerm_neg_one) (Y : K) : FreeOf2 c (TTw QQ w Y) := by
  induction w with
  | nil => exact freeOf2_lift c _
  | cons l w ih =>
    rw [List.map_cons, List.mem_cons, not_or] at hc
    unfold TTw
    split_ifs
    · exact freeOf2_mul (ih hc.2) (freeOf2_rmatrix hc.1 _)
    · exact freeOf2_mul (freeOf2_rmatrix_transpose hc.1 _) (ih hc.2)
end Formalism.FourierDecayAlt.P.Wd11
