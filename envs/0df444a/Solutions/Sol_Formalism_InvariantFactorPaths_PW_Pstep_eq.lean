-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.Pstep_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:05:55.421001+00:00
-- url     : https://prove2.me/submissions/4e85e68c-50f7-4fa1-9adf-31d0f4ee750b

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
theorem _root_.solution (S : Finset ι) (z : ι) (l : ℕ) :
    Pstep E S z l = ∑ q ∈ range (l + 1), cc K S.card q • Om E S z q := rfl
end Formalism.InvariantFactorPaths.PW
