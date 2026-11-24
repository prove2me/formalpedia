-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd11.freeOf2_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:49:22.089779+00:00
-- url     : https://prove2.me/submissions/f167df3b-1ba8-46a7-8776-649300f20eac

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
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd11
theorem _root_.solution {a : S} {M N : M2 (SlopeTestRemainingChoices S A)} (hM : FreeOf2 a M) (hN : FreeOf2 a N) :
    FreeOf2 a (M * N) := by
  intro i j k l
  rw [Matrix.mul_apply]
  exact Commute.sum_right _ _ _ fun m _ => (hM i m k l).mul_right (hN m j k l)
end Formalism.FourierDecayAlt.P.Wd11
