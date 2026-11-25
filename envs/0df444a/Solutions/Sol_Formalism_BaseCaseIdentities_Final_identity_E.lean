-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Final.identity_E
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:19:17.978746+00:00
-- url     : https://prove2.me/submissions/7fb19458-6788-4d81-8cfc-41098f3a506d

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_SecondWayHolds
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_BaseCaseFalseGeneralHolds
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_FixAll
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Theorems.Thm_Formalism_BaseCaseIdentities_identity_e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.BaseCaseIdentities Formalism.BaseCaseIdentities.Final
open Formalism.BaseCaseIdentities
namespace Formalism.BaseCaseIdentities.Final
theorem _root_.solution : IdE := identity_e
end Formalism.BaseCaseIdentities.Final
