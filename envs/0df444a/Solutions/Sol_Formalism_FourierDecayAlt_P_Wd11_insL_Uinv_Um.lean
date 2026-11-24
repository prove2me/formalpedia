-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd11.insL_Uinv_Um
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:02:42.611055+00:00
-- url     : https://prove2.me/submissions/4bc2627a-ca54-49cb-bf22-16e1b393ba8e

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_insL_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_insL_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_Uinv_mul_Um

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
theorem _root_.solution (a : S) (s : K) :
    (ins a (lift0 (Uinv (A := A) s)) : SlopeTestRemainingChoices S A) * ins a (lift0 (Um (A := A) s)) = 1 := by
  rw [← insL_mul, Uinv_mul_Um, insL_one]
end Formalism.FourierDecayAlt.P.Wd11
