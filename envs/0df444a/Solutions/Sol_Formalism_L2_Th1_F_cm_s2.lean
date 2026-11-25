-- Prove2me | solution 1 for Formalism.L2.Th1.F.cm_s2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:37:47.923968+00:00
-- url     : https://prove2.me/submissions/3b3cdb2a-aceb-4ae3-bbb4-dbbf9fd6948b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_QuasiPeriodConstIsogeny
import Theorems.Thm_Formalism_L2_Th1_F_quasiPeriodConstIsogeny_thm
import Theorems.Thm_Formalism_L2_Th1_F_cmQuasiPeriodConst_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
namespace Formalism.L2.Th1.F
theorem _root_.solution : CMQuasiPeriodConst := cmQuasiPeriodConst_of quasiPeriodConstIsogeny_thm
end Formalism.L2.Th1.F
