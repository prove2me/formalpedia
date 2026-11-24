-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd7.free_RRw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:57.657368+00:00
-- url     : https://prove2.me/submissions/8e682400-8864-4717-8870-e5f47218fcac

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_ins_free
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_free_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_free_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_freeOf2_transpose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_freeOf_transfer_word_matrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_ins_free


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd7
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd7
theorem _root_.solution {c : S} (QQ : K → M2 A) (w : List (Letter K S)) (hc : c ∉ w.map Letter.intersection_update_fsHerm_neg_one) :
    FreeOf c (RRw QQ w) := by
  induction w with
  | nil => exact free_one c
  | cons l w ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hc
    simp only [RRw]
    refine free_mul (ih hc.2) (ins_free hc.1 _ ?_)
    split_ifs
    · exact freeOf_transfer_word_matrix QQ w hc.2 _
    · exact freeOf2_transpose (freeOf_transfer_word_matrix QQ w hc.2 _)
end Formalism.FourierDecayAlt.P.Wd7
