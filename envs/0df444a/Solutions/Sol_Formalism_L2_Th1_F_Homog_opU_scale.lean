-- Prove2me | solution 1 for Formalism.L2.Th1.F.Homog.opU_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:23:47.582749+00:00
-- url     : https://prove2.me/submissions/583463c9-95cc-4b12-9238-f55ce5885fa5

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_LatticeOnly
import Theorems.Thm_Formalism_L2_Th1_F_Homog_sgStar_scale
import Theorems.Thm_Formalism_L2_Th1_F_Homog_herm_scale

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
open Formalism.L2.Th1.F.Homog
variable (L : PeriodPair) (c : ℂ) (hc : c ≠ 0)
namespace Formalism.L2.Th1.F.Homog
theorem _root_.solution (t z : ℂ) :
    opU (scalePair L c hc) (c * t) (sgStar (scalePair L c hc)) (c * z)
      = c * opU L t (sgStar L) z := by
  simp only [opU]
  rw [show c * z + c * t = c * (z + t) by ring, sgStar_scale L c hc, herm_scale L c hc,
    herm_scale L c hc]
  ring
end Formalism.L2.Th1.F.Homog
