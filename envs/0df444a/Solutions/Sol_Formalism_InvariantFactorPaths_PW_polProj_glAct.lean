-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.polProj_glAct
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:24.023748+00:00
-- url     : https://prove2.me/submissions/f886d70c-cb83-4303-86be-6d5078abd692

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_LatData
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CommProjectionHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_ZpClosedToAddSubgroup
import Theorems.Thm_Formalism_CountingSumsFrames_whc_comm
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_wL


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
theorem _root_.solution (LL L2 : Letters N) (j : ℕ) (c d : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    polProj p r L2 (glAct p LL j c d x) = glAct p LL j c d (polProj p r L2 x) :=
  Formalism.CountingSumsFrames.whc_comm _ _ (fun _ _ hx => glAct_wL LL j c d hx) _ x
end Formalism.InvariantFactorPaths.PW
