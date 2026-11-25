-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.chainWeights
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:18:14.78185+00:00
-- url     : https://prove2.me/submissions/dd98ad10-bdfc-4ff1-9347-2be9194a1852

import Definitions.Def_Formalism_BranchSandwichDivisors_DivFromPassageAndNorm
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_GlobalBoundRefinements
import Definitions.Def_Formalism_BranchSandwichDivisors_ChainDenominatorCoupled
import Theorems.Thm_Formalism_BranchingDeterminantCap_chain_weights


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
theorem _root_.solution : ChainWeights := chain_weights
end Formalism.BranchingDeterminantCap
