-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd11.free_bT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:10:55.036973+00:00
-- url     : https://prove2.me/submissions/10a4e862-ae49-4735-be8c-9de0a5d8d4cc

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_free_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_free_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_free_insL

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
theorem _root_.solution (σ : Site A) (w : List (Letter K S)) (c : S) (hc : c ∉ w.map Letter.intersection_update_fsHerm_neg_one) :
    FreeOf c (bT σ w) := by
  induction w with
  | nil => exact free_one c
  | cons l w ih =>
    rw [List.map_cons, List.mem_cons, not_or] at hc
    exact free_mul (free_insL hc.1 _) (ih hc.2)
end Formalism.FourierDecayAlt.P.Wd11
