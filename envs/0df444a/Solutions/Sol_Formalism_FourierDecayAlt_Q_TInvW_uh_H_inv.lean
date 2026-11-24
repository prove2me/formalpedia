-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.uh_H_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:57:51.003047+00:00
-- url     : https://prove2.me/submissions/97238e5d-3ebd-464f-a828-18f113f4af5c

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
theorem _root_.solution {s : Mx k r} (hs : s ∈ UH (Hpk k r)) (hu : s * s⁻¹ = 1) :
    Hpk k r * s⁻¹ = sᴴ * Hpk k r := by
  have hs' : sᴴ * Hpk k r * s = Hpk k r := hs
  calc Hpk k r * s⁻¹ = sᴴ * Hpk k r * s * s⁻¹ := by rw [hs']
    _ = sᴴ * Hpk k r := by rw [mul_assoc (sᴴ * Hpk k r), hu, mul_one]
end Formalism.FourierDecayAlt.Q.TInvW
