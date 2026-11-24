-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.sum_posL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:56:36.805246+00:00
-- url     : https://prove2.me/submissions/52c90bce-2358-457f-a781-f1530e3cc0e8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_TransferInvarianceRestriction
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_posL_inj


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
theorem _root_.solution {M : Type*} [AddCommMonoid M] {i : Fin (r + 1)} (F : Fin (2 * r + k + 1) → M)
    (hF : ∀ q, (∀ c, q ≠ posL k r i c) → F q = 0) :
    ∑ q, F q = ∑ c : Fin (mdim k r i), F (posL k r i c) := (Fintype.sum_of_injective (posL k r i) (fun _ _ h => posL_inj h) _ F
    (fun q hq => hF q (fun c hc => hq ⟨c, hc.symm⟩)) (fun _ => rfl)).symm
end Formalism.FourierDecayAlt.Q.TInvW
