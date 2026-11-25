-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Final.identity_of_base_case
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:19:20.570049+00:00
-- url     : https://prove2.me/submissions/84bffc31-cfe1-4db0-b52a-7c845a67e3ff

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_SecondWayHolds
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_BaseCaseFalseGeneralHolds
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_FixAll
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Theorems.Thm_Formalism_BaseCaseIdentities_identity_twenty_d


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
theorem _root_.solution : PowMulThreeEighthsIdentity := identity_twenty_d
end Formalism.BaseCaseIdentities.Final
