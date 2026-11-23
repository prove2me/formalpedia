-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.stepDiiiRecord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:27:20.834798+00:00
-- url     : https://prove2.me/submissions/49cd0808-14b0-4896-9b77-ca14df34c2d1

import Definitions.Def_Formalism_BranchSandwichDivisors_DivFromPassageAndNorm
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_GlobalBoundRefinements
import Definitions.Def_Formalism_BranchSandwichDivisors_ChainDenominatorCoupled

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution : StepDiiiRecord := third_descent_inequality
end Formalism.BranchingDeterminantCap
