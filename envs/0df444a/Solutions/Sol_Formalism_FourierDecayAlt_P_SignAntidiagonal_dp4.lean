-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.dp4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:41:14.382315+00:00
-- url     : https://prove2.me/submissions/da3519fa-09c0-4a8e-9237-ca4555b08646

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainFirstIdentity
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RightDerivativeRulePsi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants
variable {k r : ℕ} (z' : Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1))
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution (hp : r + k < p.val) (hq : r + k < q.val) : dpsiP k r z' p q = if q.val = p.val + 1 then 1 else 0 := by
  rw [dpsiP, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos ⟨hp, hq⟩]
end Formalism.FourierDecayAlt.P.SignAntidiagonal
