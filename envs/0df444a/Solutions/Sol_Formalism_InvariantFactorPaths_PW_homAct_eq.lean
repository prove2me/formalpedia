-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.homAct_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:58:10.999847+00:00
-- url     : https://prove2.me/submissions/fc8ad958-f0e4-4ac2-a352-e7e22cc7b7cf

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_HomRelationHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_homAct_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_postC_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_preC_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Finset
variable {K V W ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [DecidableEq ι]
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (EV : ι → ι → Module.End K V) (EW : ι → ι → Module.End K W) (a b : ι) :
    homAct EV EW a b = postC (EW a b) + -preC (EV a b) := by
  ext φ x
  simp only [homAct_apply, LinearMap.add_apply, LinearMap.neg_apply, postC_apply, preC_apply, sub_eq_add_neg]
end Formalism.InvariantFactorPaths.PW
