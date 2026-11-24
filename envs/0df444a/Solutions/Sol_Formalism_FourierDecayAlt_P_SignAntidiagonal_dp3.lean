-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.dp3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:41:13.318258+00:00
-- url     : https://prove2.me/submissions/b198409e-b1fc-4b37-b356-c085dc820add

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
theorem _root_.solution (hp1 : r ≤ p.val) (hp2 : p.val ≤ r + k) (hq : r + k < q.val) :
    dpsiP k r z' p q = if q.val = r + k + 1 then herm (Hpk k r) (bvec p) z' else 0 := by
  rw [dpsiP, if_neg (by omega), if_neg (by omega), if_pos ⟨hp1, hp2, hq⟩]
end Formalism.FourierDecayAlt.P.SignAntidiagonal
