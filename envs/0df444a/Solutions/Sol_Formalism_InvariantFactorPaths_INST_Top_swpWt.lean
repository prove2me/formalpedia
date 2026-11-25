-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.INST.Top.swpWt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:28:55.002747+00:00
-- url     : https://prove2.me/submissions/53328c85-1e43-4141-b94d-8b067925af4f

import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_GlFirstLineDividedPowers
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_SwappedHighestWeightNeZero
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_Spread
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_Descent
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_Ascent
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_Assemble
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_FinalW
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_swap_weight_compat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.INST Formalism.InvariantFactorPaths.INST.Top
namespace Formalism.InvariantFactorPaths.INST.Top
theorem _root_.solution : SwpWt := swap_weight_compat
end Formalism.InvariantFactorPaths.INST.Top
