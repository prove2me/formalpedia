-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.polProj_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:26.386241+00:00
-- url     : https://prove2.me/submissions/fe3eb2f4-c825-44ea-a885-67bc13099a14

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
theorem _root_.solution (L2 : Letters N) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    polProj p r L2 x ∈ Pol p r L2 := by
  rw [pol_iff]; exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
end Formalism.InvariantFactorPaths.PW
