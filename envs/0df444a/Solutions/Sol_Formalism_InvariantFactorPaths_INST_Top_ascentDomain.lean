-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.INST.Top.ascentDomain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:28:52.767307+00:00
-- url     : https://prove2.me/submissions/a424e608-c35e-4c8a-8ad5-36d6cc2d355c

import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_GlFirstLineDividedPowers
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_SwappedHighestWeightNeZero
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_Spread
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_Descent
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_Ascent
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_Assemble
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_FinalW
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_ascent_domain_holds


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
theorem _root_.solution : AscentDomain := ascent_domain_holds
end Formalism.InvariantFactorPaths.INST.Top
