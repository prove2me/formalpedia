-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd11.insL_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:42:49.219138+00:00
-- url     : https://prove2.me/submissions/f2d353ca-9c2e-4969-8930-1b8944746d5a

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_freeOf2_lift
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_liftMatrix_conjTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_star


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
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd11
theorem _root_.solution [StarRing A] (a : S) (M : M2 A) :
    star (ins a (lift0 M) : SlopeTestRemainingChoices S A) = ins a (lift0 Mᴴ) := by
  rw [ins_star a _ (freeOf2_lift a M), liftMatrix_conjTranspose]
end Formalism.FourierDecayAlt.P.Wd11
