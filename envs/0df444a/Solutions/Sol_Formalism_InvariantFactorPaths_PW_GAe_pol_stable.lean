-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.GAe_pol_stable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:57.959147+00:00
-- url     : https://prove2.me/submissions/508a80be-614f-46a3-946c-38074f142181

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_HasLatBasis
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_pol


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
variable {p : ℕ} [Fact p.Prime] {N r n : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (LL L2 : Letters N) (j : ℕ) (e : Fin n ↪o Fin r) :
    (GAe p LL j e).Stable (Pol p r L2) :=
  fun a b _ hx => glAct_pol LL L2 j (e a) (e b) hx
end Formalism.InvariantFactorPaths.PW
