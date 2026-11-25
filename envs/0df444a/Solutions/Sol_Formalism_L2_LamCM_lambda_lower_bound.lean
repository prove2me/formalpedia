-- Prove2me | solution 1 for Formalism.L2.LamCM.lambda_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:09:48.511665+00:00
-- url     : https://prove2.me/submissions/b08a678e-a4cf-4ef2-872b-32229dcbdda4

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_DetValuationLeOne
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ExistsEvalNeZeroOfTotalDegreeLt
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ExistsMonicIrreducibleCardGt
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_FiniteDetAddSmulOneEqZero
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_LargeResidueExtensionLemma
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_HermitianFormGramBlockBasis
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_LambdaLowerBound
import Theorems.Thm_Formalism_L2_LamCM_Step5_of
import Theorems.Thm_Formalism_L2_LamCM_lambda_key_formula


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.LamCM
namespace Formalism.L2.LamCM
theorem _root_.solution : Step5 := Step5_of lambda_key_formula
end Formalism.L2.LamCM
