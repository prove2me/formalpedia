-- Prove2me | solution 1 for Formalism.L2.Th1.F.Homog.wp_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:24:00.665798+00:00
-- url     : https://prove2.me/submissions/8f861c96-f6b3-4bea-8576-4f9d0f4ff6ee

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_LatticeOnly
import Theorems.Thm_Formalism_L2_Th1_F_Homog_tsum_scale

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
theorem _root_.solution (z : ℂ) :
    (scalePair L c hc).weierstrassP (c * z) = (c ^ 2)⁻¹ * L.weierstrassP z := by
  simp only [PeriodPair.weierstrassP]
  rw [tsum_scale L c hc (fun w => 1 / (c * z - w) ^ 2 - 1 / w ^ 2), ← tsum_mul_left]
  congr 1
  funext l
  try dsimp only
  rw [show c * z - c * (l : ℂ) = c * (z - l) by ring]
  simp only [one_div, mul_inv, mul_pow]
  ring
end Formalism.L2.Th1.F.Homog
