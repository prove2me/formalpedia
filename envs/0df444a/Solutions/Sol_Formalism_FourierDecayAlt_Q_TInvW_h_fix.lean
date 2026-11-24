-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.h_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:56:34.539628+00:00
-- url     : https://prove2.me/submissions/90cd45c6-9ec9-4cc2-955c-f2a4fa346e0d

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
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} {i : Fin (r + 1)} {h : Mx k r} (hh : h ∈ UWset k r z) :
    h *ᵥ fvec k r z i = fvec k r z i := by
  simp only [UWset, Set.mem_setOf_eq] at hh
  unfold fvec
  split_ifs with hi
  · exact (hh.2.1 _).1
  · exact hh.2.2
end Formalism.FourierDecayAlt.Q.TInvW
