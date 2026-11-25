-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.INST.Top.descentZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:17:09.647383+00:00
-- url     : https://prove2.me/submissions/f92bb71b-259e-462e-adbc-1cbe0d146a76

import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_GlFirstLineDividedPowers
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_SwappedHighestWeightNeZero
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_Spread
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_Descent
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_Ascent
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_Assemble
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_FinalW
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_descent_over_integers


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
theorem _root_.solution : DescentZ := descent_over_integers
end Formalism.InvariantFactorPaths.INST.Top
