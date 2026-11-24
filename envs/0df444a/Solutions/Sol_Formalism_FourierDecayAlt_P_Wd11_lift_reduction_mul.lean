-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd11.lift_reduction_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:51:05.916608+00:00
-- url     : https://prove2.me/submissions/8f1d528a-2f01-443b-b5e9-47b48d810b08

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
theorem _root_.solution (M N : M2 A) : (lift0 (M * N) : M2 (SlopeTestRemainingChoices S A)) = lift0 M * lift0 N := by
  show (M * N).map (Matrix.scalar (Ix S)) =
    M.map (Matrix.scalar (Ix S)) * N.map (Matrix.scalar (Ix S))
  exact Matrix.map_mul
end Formalism.FourierDecayAlt.P.Wd11
