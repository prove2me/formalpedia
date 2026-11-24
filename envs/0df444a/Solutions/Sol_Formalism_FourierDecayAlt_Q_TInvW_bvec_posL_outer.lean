-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.bvec_posL_outer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:38:01.01751+00:00
-- url     : https://prove2.me/submissions/eb6c150c-93cb-4098-8538-2703b07167af

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_TransferInvarianceRestriction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.TInvW
theorem _root_.solution {i : Fin (r + 1)} (a : Fin (mdim k r i)) (q : Fin (2 * r + k + 1))
    (hq : ∀ c, q ≠ posL k r i c) : bvec q (posL k r i a) = 0 ∧ bvec (posL k r i a) q = 0 := ⟨by simp [bvec, Pi.single_apply, hq a, (hq a).symm], by simp [bvec, Pi.single_apply, hq a, (hq a).symm]⟩
end Formalism.FourierDecayAlt.Q.TInvW
