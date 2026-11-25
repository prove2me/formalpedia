-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.orthogonal_sandwich_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:39:59.662491+00:00
-- url     : https://prove2.me/submissions/b6e9785a-7fe3-4f09-b34b-1cf68ac6e559

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MapScale
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_OrthSum
import Theorems.Thm_Formalism_BranchingDeterminantCap_orthSandwich_of
import Theorems.Thm_Formalism_BranchingDeterminantCap_scale_sandwich_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Matrix
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution : OrthSandwich := orthSandwich_of scale_sandwich_bound
end Formalism.BranchingDeterminantCap
