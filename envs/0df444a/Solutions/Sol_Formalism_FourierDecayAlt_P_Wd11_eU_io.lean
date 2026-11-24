-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd11.eU_io
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:50:49.260902+00:00
-- url     : https://prove2.me/submissions/28cdff04-7936-4780-805e-4cd075b6bfc2

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_eU_apply


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
theorem _root_.solution (a : S) (i j : Fin 2) (x : A) : Commute (eU a i j : SlopeTestRemainingChoices S A) (io x) := by
  show eU a i j * io x = io x * eU a i j
  ext u v
  unfold io
  rw [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, eU_apply]
  split_ifs <;> simp
end Formalism.FourierDecayAlt.P.Wd11
