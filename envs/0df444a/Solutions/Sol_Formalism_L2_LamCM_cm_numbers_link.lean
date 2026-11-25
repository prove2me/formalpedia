-- Prove2me | solution 1 for Formalism.L2.LamCM.cm_numbers_link
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:09:13.842107+00:00
-- url     : https://prove2.me/submissions/03adbc4f-51ea-48cd-983d-74918f124917

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_OneLeAbsNormOfLeOne
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ProdMulLeDetIdeal
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ValuationLeOfEqAlgebraMap
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_AbsNormSpanGalois
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Theorems.Thm_Formalism_L2_LamCM_CMNumbersLink_of
import Theorems.Thm_Formalism_L2_LamCM_detLineAdmissible
import Theorems.Thm_Formalism_L2_LamCM_hadamardIdeals


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
theorem _root_.solution : CMNumbersLink := CMNumbersLink_of hadamardIdeals detLineAdmissible
end Formalism.L2.LamCM
