-- Prove2me | solution 1 for Formalism.L2.Th1.F.iotaExists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:45:06.79882+00:00
-- url     : https://prove2.me/submissions/9e1277ed-6358-4c44-996e-88a1b9888952

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_IsogenyFormulaInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HasCMByStable
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_WeierstrassNumeratorDenominator
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Bridge
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_MkLeOfDenseRange
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Universal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinRecursion
import Theorems.Thm_Formalism_L2_Th1_F_iotaExists_thm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
namespace Formalism.L2.Th1.F
theorem _root_.solution : IotaExists := iotaExists_thm
end Formalism.L2.Th1.F
