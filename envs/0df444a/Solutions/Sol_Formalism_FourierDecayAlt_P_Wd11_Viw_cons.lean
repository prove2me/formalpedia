-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd11.Viw_cons
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:51:10.801794+00:00
-- url     : https://prove2.me/submissions/a9c533b0-8b1c-4b7d-96e7-944c02a4056f

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix

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
theorem _root_.solution (fi : A) (s : K) (l : Letter K S) (w : List (Letter K S)) :
    Viw fi s (l :: w) =
      ins l.intersection_update_fsHerm_neg_one (lift0 (Um (A := A) (if l.plus then s else star s))) * Viw fi s w := by
  show ins l.intersection_update_fsHerm_neg_one (lift0 (Um (A := A) (if l.plus then s else star s))) * UUw s w * io fi =
    ins l.intersection_update_fsHerm_neg_one (lift0 (Um (A := A) (if l.plus then s else star s))) * (UUw s w * io fi)
  exact mul_assoc _ _ _
end Formalism.FourierDecayAlt.P.Wd11
