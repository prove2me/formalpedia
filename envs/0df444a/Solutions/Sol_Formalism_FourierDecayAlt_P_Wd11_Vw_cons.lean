-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd11.Vw_cons
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:25:28.873269+00:00
-- url     : https://prove2.me/submissions/1ada5723-c673-493c-bf59-e1ba2a05c14f

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_free_io
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_comm_insL
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_cen_Uinv

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
theorem _root_.solution (f : A) (s : K) (l : Letter K S) (w : List (Letter K S)) :
    Vw f s (l :: w) =
      ins l.intersection_update_fsHerm_neg_one (lift0 (Uinv (A := A) (if l.plus then s else star s))) * Vw f s w := by
  show io f * (ins l.intersection_update_fsHerm_neg_one (lift0 (Uinv (A := A) (if l.plus then s else star s))) * UUiw s w) =
    ins l.intersection_update_fsHerm_neg_one (lift0 (Uinv (A := A) (if l.plus then s else star s))) * (io f * UUiw s w)
  exact (comm_insL (cen_Uinv _) (free_io _ f)).left_comm _
end Formalism.FourierDecayAlt.P.Wd11
