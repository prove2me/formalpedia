-- Prove2me | solution 1 for Formalism.L2.Th1.F.taylorSgStar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:28:52.699801+00:00
-- url     : https://prove2.me/submissions/082dfc9b-c021-405c-a7d1-5604ac26484d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstIsogeny
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IntegerEndomorphismInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_IsogenyFormulaInstance
import Theorems.Thm_Formalism_L2_Th1_F_taylorRing
import Theorems.Thm_Formalism_L2_Th1_F_taylorExp
import Theorems.Thm_Formalism_L2_Th1_F_taylorSigma
import Theorems.Thm_Formalism_L2_Th1_F_sigmaEntire
import Theorems.Thm_Formalism_L2_Th1_F_taylorSgStar_of


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
theorem _root_.solution : TaylorSgStar := taylorSgStar_of taylorSigma taylorRing taylorExp sigmaEntire
end Formalism.L2.Th1.F
