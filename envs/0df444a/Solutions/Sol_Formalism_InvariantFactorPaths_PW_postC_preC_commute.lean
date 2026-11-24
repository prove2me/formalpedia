-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.postC_preC_commute
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:50:01.997752+00:00
-- url     : https://prove2.me/submissions/70ef5eaa-a252-4a7b-920c-31a8d1bfaa78

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
theorem _root_.solution (X : Module.End K W) (Y : Module.End K V) :
    Commute (postC (V := V) X) (preC (W := W) Y) := by
  show postC (V := V) X * preC (W := W) Y = preC (W := W) Y * postC (V := V) X
  ext φ x
  rfl
end Formalism.InvariantFactorPaths.PW
