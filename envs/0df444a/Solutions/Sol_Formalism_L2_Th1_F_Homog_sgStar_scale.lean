-- Prove2me | solution 1 for Formalism.L2.Th1.F.Homog.sgStar_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:18:48.101454+00:00
-- url     : https://prove2.me/submissions/3d52d25f-8c49-495b-81cd-929f0427a04d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_LatticeOnly
import Theorems.Thm_Formalism_L2_Th1_F_Homog_wSigma_scale
import Theorems.Thm_Formalism_L2_Th1_F_Homog_quasiPeriodConst_scale

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
theorem _root_.solution (z : ℂ) : sgStar (scalePair L c hc) (c * z) = c * sgStar L z := by
  simp only [sgStar]
  rw [wSigma_scale L c hc, quasiPeriodConst_scale L c hc]
  have hcc : (c ^ 2)⁻¹ * c ^ 2 = 1 := inv_mul_cancel₀ (pow_ne_zero 2 hc)
  have he : -((c ^ 2)⁻¹ * s2 L) * (c * z) ^ 2 / 2 = -(s2 L) * z ^ 2 / 2 := by
    linear_combination (-(s2 L) * z ^ 2 / 2) * hcc
  rw [he]
  ring
end Formalism.L2.Th1.F.Homog
