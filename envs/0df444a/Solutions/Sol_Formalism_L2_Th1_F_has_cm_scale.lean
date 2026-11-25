-- Prove2me | solution 1 for Formalism.L2.Th1.F.has_cm_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:26:41.216686+00:00
-- url     : https://prove2.me/submissions/87d4baa8-ecba-4b63-80ec-566afbfd91d3

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstIsogeny
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HasCMByIsogenyOf
import Theorems.Thm_Formalism_L2_Th1_F_hasCMByScale_of
import Theorems.Thm_Formalism_L2_Th1_F_homogeneity


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
open Formalism.L2.Th1.CM (omegaK HasCMBy)
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
namespace Formalism.L2.Th1.F
theorem _root_.solution : HasCMByScale := hasCMByScale_of homogeneity
end Formalism.L2.Th1.F
