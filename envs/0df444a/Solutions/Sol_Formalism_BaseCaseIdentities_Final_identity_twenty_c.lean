-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Final.identity_twenty_c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:23:44.748234+00:00
-- url     : https://prove2.me/submissions/58359711-ef89-4faa-8e60-88fea25d4226

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_SecondWayHolds
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_BaseCaseFalseGeneralHolds
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_FixAll
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Theorems.Thm_Formalism_BaseCaseIdentities_sqMulIdentity_statement


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
theorem _root_.solution : SqMulIdentity := sqMulIdentity_statement
end Formalism.BaseCaseIdentities.Final
