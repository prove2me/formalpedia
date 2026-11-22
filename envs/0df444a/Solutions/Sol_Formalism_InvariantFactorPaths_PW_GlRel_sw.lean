-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.GlRel.sw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:21:58.610172+00:00
-- url     : https://prove2.me/submissions/56f6ce8b-2a13-4c3f-be49-7b24a9087a21

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInv

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
variable {K W ι : Type} [Field K] [AddCommGroup W] [Module K W] [DecidableEq ι]
variable {E : ι → ι → Module.End K W}
namespace Formalism.InvariantFactorPaths.PW
namespace GlRel
theorem _root_.solution (h : GlRel E) (a b c d : ι) :
    E a b * E c d = E c d * E a b + ((if b = c then E a d else 0) - (if d = a then E c b else 0)) := by
  exact sub_eq_iff_eq_add'.mp (h a b c d)
end GlRel
end Formalism.InvariantFactorPaths.PW
