-- Prove2me | solution 1 for Formalism.L2.Th1.F.th0Basic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:54:54.400691+00:00
-- url     : https://prove2.me/submissions/bca44e70-f74b-48c0-b199-b17bcf638585

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_SigmaLogDeriv2
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_QuasiPeriodConstUniqueOf
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_OperatorUComm
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SgStar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HermHalfRight
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Theorems.Thm_Formalism_L2_Th1_F_altEInt
import Theorems.Thm_Formalism_L2_Th1_F_sgStarQuasi
import Theorems.Thm_Formalism_L2_Th1_F_sgStarBasic
import Theorems.Thm_Formalism_L2_Th1_F_th0Basic_of


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
theorem _root_.solution : ThetaZeroBasic := th0Basic_of sgStarBasic sgStarQuasi altEInt
end Formalism.L2.Th1.F
