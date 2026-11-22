-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.homAct_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:22:23.617542+00:00
-- url     : https://prove2.me/submissions/38451cfa-ec7e-4e74-a8f0-8f17a3a4805d

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_HomRelationHolds

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
theorem _root_.solution (EV : ι → ι → Module.End K V) (EW : ι → ι → Module.End K W) (a b : ι) (φ : V →ₗ[K] W) (x : V) :
    homAct EV EW a b φ x = EW a b (φ x) - φ (EV a b x) := rfl
end Formalism.InvariantFactorPaths.PW
