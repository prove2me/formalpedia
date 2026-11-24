-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd11.insL_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:42:43.440826+00:00
-- url     : https://prove2.me/submissions/ef697b77-f111-4271-b8ee-c3e2db56602b

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_freeOf2_lift
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_lift_reduction_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_mul


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
theorem _root_.solution (a : S) (M N : M2 A) :
    (ins a (lift0 (M * N)) : SlopeTestRemainingChoices S A) = ins a (lift0 M) * ins a (lift0 N) := by
  rw [lift_reduction_mul, ins_mul a _ _ (freeOf2_lift a M)]
end Formalism.FourierDecayAlt.P.Wd11
