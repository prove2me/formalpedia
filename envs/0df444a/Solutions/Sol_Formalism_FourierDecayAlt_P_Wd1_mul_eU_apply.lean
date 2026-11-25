-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd1.mul_eU_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:59:58.1117+00:00
-- url     : https://prove2.me/submissions/888958f4-0d93-42fa-b1f7-2a6f52e09efe

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Wd1_eU_apply__48c6d160d783

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd1
open Matrix Formalism.FourierDecayAlt.Wd
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd1
theorem _root_.solution (a : S) (i j : Fin 2) (B : SlopeTestRemainingChoices S A) (x y : Ix S) :
    (B * (eU a i j : SlopeTestRemainingChoices S A)) x y = if y a = j then B x (Function.update y a i) else 0 := by
  simp only [Matrix.mul_apply, eU_apply', mul_ite, mul_one, mul_zero]
  by_cases hy : y a = j <;> simp [hy]
end Formalism.FourierDecayAlt.P.Wd1
