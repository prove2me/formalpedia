-- Prove2me | solution 1 for Formalism.L2.Th1.F.Homog.normalizedTheta_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:32:42.901389+00:00
-- url     : https://prove2.me/submissions/5c4bf314-1b8a-4315-8f3c-d0b2fec5d67e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_LatticeOnly
import Theorems.Thm_Formalism_L2_Th1_F_Homog_opU_scale

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
theorem _root_.solution (t z : ℂ) : th0 (scalePair L c hc) (c * t) (c * z) = th0 L t z := by
  simp only [th0]
  have h0 := opU_scale L c hc t 0
  rw [mul_zero] at h0
  rw [opU_scale L c hc t z, h0]
  exact mul_div_mul_left _ _ hc
end Formalism.L2.Th1.F.Homog
