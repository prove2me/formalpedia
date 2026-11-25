-- Prove2me | solution 1 for Formalism.L2.Th1.F.homogeneity_thm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:41:43.937152+00:00
-- url     : https://prove2.me/submissions/43f45eb8-99a2-4034-88e6-7d0599fbd3ca

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_LatticeOnly
import Theorems.Thm_Formalism_L2_Th1_F_Homog_wZeta_scale
import Theorems.Thm_Formalism_L2_Th1_F_Homog_wSigma_scale
import Theorems.Thm_Formalism_L2_Th1_F_Homog_wp_scale
import Theorems.Thm_Formalism_L2_Th1_F_Homog_G_scale
import Theorems.Thm_Formalism_L2_Th1_F_Homog_wEta_scale
import Theorems.Thm_Formalism_L2_Th1_F_Homog_area_scale
import Theorems.Thm_Formalism_L2_Th1_F_Homog_quasiPeriodConst_scale
import Theorems.Thm_Formalism_L2_Th1_F_Homog_sgStar_scale
import Theorems.Thm_Formalism_L2_Th1_F_Homog_normalizedTheta_scale

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
theorem _root_.solution : Homogeneity := by
  intro L c hc
  refine ⟨Homog.mem_scale L c hc, Homog.wZeta_scale L c hc, Homog.wSigma_scale L c hc,
    Homog.wp_scale L c hc, Homog.wEta_scale L c hc, Homog.area_scale L c hc, Homog.quasiPeriodConst_scale L c hc,
    Homog.sgStar_scale L c hc, Homog.normalizedTheta_scale L c hc, ?_, ?_⟩
  · first
      | (simp only [PeriodPair.g₂, Homog.G_scale L c hc]
         ring)
      | (unfold PeriodPair.g₂
         done)
  · first
      | (simp only [PeriodPair.g₃, Homog.G_scale L c hc]
         ring)
      | (unfold PeriodPair.g₃
         done)
end Formalism.L2.Th1.F
