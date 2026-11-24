-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd7.freeOf_transfer_word_matrix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:18:39.261886+00:00
-- url     : https://prove2.me/submissions/287680bf-ef75-450c-8c5c-4b1ce8faa7e9

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_freeOf2_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_freeOf2_lift
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_freeOf_positive_word_matrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_freeOf_negative_word_matrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_TTw_factor

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
theorem _root_.solution {c : S} (QQ : K → M2 A) (w : List (Letter K S)) (hc : c ∉ w.map Letter.intersection_update_fsHerm_neg_one)
    (Y : K) : FreeOf2 c (TTw QQ w Y) := by
  rw [TTw_factor]
  exact freeOf2_mul (freeOf2_mul (freeOf_negative_word_matrix w hc Y) (freeOf2_lift c _)) (freeOf_positive_word_matrix w hc Y)
end Formalism.FourierDecayAlt.P.Wd7
