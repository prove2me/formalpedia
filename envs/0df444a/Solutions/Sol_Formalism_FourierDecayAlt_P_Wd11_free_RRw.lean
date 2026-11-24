-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd11.free_RRw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:10:56.073799+00:00
-- url     : https://prove2.me/submissions/6ba24ab7-f110-4551-8614-d9c5bbf8d333

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_free_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_free_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_freeOf2_transpose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_freeOf_transfer_word_matrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_free


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
    (hc : c ∉ w.map Letter.intersection_update_fsHerm_neg_one) : FreeOf c (RRw QQ w) := by
  induction w with
  | nil => exact free_one c
  | cons l w ih =>
    rw [List.map_cons, List.mem_cons, not_or] at hc
    unfold RRw
    refine free_mul (ih hc.2) (ins_free hc.1 _ ?_)
    split_ifs
    · exact freeOf_transfer_word_matrix QQ w c hc.2 _
    · exact freeOf2_transpose (freeOf_transfer_word_matrix QQ w c hc.2 _)
end Formalism.FourierDecayAlt.P.Wd11
