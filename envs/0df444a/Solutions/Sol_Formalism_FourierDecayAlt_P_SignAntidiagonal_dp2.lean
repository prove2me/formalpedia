-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.dp2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:39:03.528677+00:00
-- url     : https://prove2.me/submissions/b96b24ff-7127-4728-ac13-e534530431d5

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
theorem _root_.solution (hp : p.val < r) (hq1 : r ≤ q.val) (hq2 : q.val ≤ r + k) :
    dpsiP k r z' p q = if p.val + 1 = r then z' q else 0 := by
  rw [dpsiP, if_neg (by omega), if_pos ⟨hp, hq1, hq2⟩]
end Formalism.FourierDecayAlt.P.SignAntidiagonal
