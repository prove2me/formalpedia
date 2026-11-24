-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.glev_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:15:27.605796+00:00
-- url     : https://prove2.me/submissions/411fdd5a-285f-4cfa-9537-14c77e0fde6c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_TransferInvarianceRestriction
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_glev_fix_outer

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
theorem _root_.solution {i : Fin (r + 1)} {g : Mx k r} (hg : g ∈ Glev k r i) (p q : Fin (2 * r + k + 1))
    (hq : ∀ c, q ≠ posL k r i c) : g p q = bvec q p := by
  rw [← congrFun (glev_fix_outer hg q hq) p]
  simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply]
end Formalism.FourierDecayAlt.Q.TInvW
