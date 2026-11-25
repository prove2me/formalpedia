-- Prove2me | solution 1 for Formalism.L2.Th1.F.quasiPeriodConstIsogeny_thm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:22:04.42885+00:00
-- url     : https://prove2.me/submissions/b298c915-da9d-45e4-aee2-6e90d3ed13f6

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_QuasiPeriodConstIsogeny
import Theorems.Thm_Formalism_L2_Th1_F_quasiPeriodConstIsogeny_of
import Theorems.Thm_Formalism_L2_Th1_F_etaSplit
import Theorems.Thm_Formalism_L2_Th1_F_isogenyP
import Theorems.Thm_Formalism_L2_Th1_F_kerRepsCard
import Theorems.Thm_Formalism_L2_Th1_F_zetaHasDeriv
import Theorems.Thm_Formalism_L2_Th1_F_zetaQuasi


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
theorem _root_.solution : QuasiPeriodConstIsogeny := quasiPeriodConstIsogeny_of isogenyP zetaHasDeriv zetaQuasi etaSplit kerRepsCard
end Formalism.L2.Th1.F
