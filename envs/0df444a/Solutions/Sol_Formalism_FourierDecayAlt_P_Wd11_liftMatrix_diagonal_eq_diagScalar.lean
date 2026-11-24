-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd11.liftMatrix_diagonal_eq_diagScalar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:51:02.690293+00:00
-- url     : https://prove2.me/submissions/6f116823-a7fb-4d75-b339-015fe5be1e65

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
theorem _root_.solution (f : A) : (lift0 (Matrix.diagonal fun _ => f) : M2 (SlopeTestRemainingChoices S A)) = d0 (io f) := by
  show (Matrix.diagonal fun _ => f).map (Matrix.scalar (Ix S)) = _
  rw [Matrix.diagonal_map (map_zero _)]
  rfl
end Formalism.FourierDecayAlt.P.Wd11
