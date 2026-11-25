-- Prove2me | solution 1 for Formalism.L2.Th1.F.th0LogDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:22:36.713889+00:00
-- url     : https://prove2.me/submissions/2cdd9254-9e05-4164-8518-36590414f3f7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_SigmaLogDeriv2
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_QuasiPeriodConstUniqueOf
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_OperatorUComm
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SgStar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HermHalfRight
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Theorems.Thm_Formalism_L2_Th1_F_etaSplit
import Theorems.Thm_Formalism_L2_Th1_F_sigmaLogDeriv
import Theorems.Thm_Formalism_L2_Th1_F_th0LogDeriv_of
import Theorems.Thm_Formalism_L2_Th1_F_zetaOdd
import Theorems.Thm_Formalism_L2_Th1_F_zetaQuasi


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
theorem _root_.solution : ThetaZeroLogDerivative := th0LogDeriv_of sigmaLogDeriv etaSplit zetaQuasi zetaOdd
end Formalism.L2.Th1.F
