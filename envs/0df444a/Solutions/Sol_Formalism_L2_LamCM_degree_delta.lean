-- Prove2me | solution 1 for Formalism.L2.LamCM.degree_delta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:09:17.249777+00:00
-- url     : https://prove2.me/submissions/9a11b001-ca11-4fb7-89fa-772a3e555bda

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_OneLeAbsNormOfLeOne
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ProdMulLeDetIdeal
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ValuationLeOfEqAlgebraMap
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_AbsNormSpanGalois
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Theorems.Thm_Formalism_L2_LamCM_DegDe_of
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
theorem _root_.solution : DegDe := DegDe_of hadamardIdeals detLineAdmissible
end Formalism.L2.LamCM
