-- Prove2me | solution 1 for Formalism.L2.Th1.F.Homog.wZeta_scale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:28:36.532916+00:00
-- url     : https://prove2.me/submissions/a77c2117-f73f-4d13-bcc1-92d332064b7c

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
theorem _root_.solution (z : ℂ) : wZeta (scalePair L c hc) (c * z) = c⁻¹ * wZeta L z := by
  simp only [wZeta]
  rw [tsum_scale L c hc (fun w => 1 / (c * z - w) + 1 / w + c * z / w ^ 2), ← tsum_mul_left]
  congr 1
  funext l
  try dsimp only
  have e : c * z - c * (l : ℂ) = c * (z - l) := by ring
  have hc2 : c * (c ^ 2)⁻¹ = c⁻¹ := by
    rw [pow_two, mul_inv, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  rw [e]
  simp only [one_div, mul_inv, div_eq_mul_inv, mul_pow]
  linear_combination (z * ((l : ℂ) ^ 2)⁻¹) * hc2
end Formalism.L2.Th1.F.Homog
