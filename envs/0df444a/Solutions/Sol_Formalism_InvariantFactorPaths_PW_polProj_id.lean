-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.polProj_id
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:01:17.889947+00:00
-- url     : https://prove2.me/submissions/fe3a907f-365d-44dd-901d-63c49e47a356

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_LatData
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CommProjectionHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_ZpClosedToAddSubgroup
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_pol_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (L2 : Letters N) {x : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hx : x ∈ Pol p r L2) :
    polProj p r L2 x = x := by
  rw [pol_iff] at hx
  rw [polProj, weightedHomogeneousComponent_of_mem hx, if_pos rfl]
end Formalism.InvariantFactorPaths.PW
