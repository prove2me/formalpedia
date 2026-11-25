-- Prove2me | solution 1 for Formalism.L2.Th1.F.Homog.wEta_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:01:43.815198+00:00
-- url     : https://prove2.me/submissions/9e81471a-1458-4542-9e62-693e4f616cc6

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_LatticeOnly
import Theorems.Thm_Formalism_L2_Th1_F_Homog_wZeta_scale
import Theorems.Thm_P2M_Formalism_L2_Th1_F_Homog_wEta_basis__f3ec1ad0cd44
import Theorems.Thm_P2M_Formalism_L2_Th1_F_Homog_wEta_basis__9ee8d3c65504
import Theorems.Thm_Formalism_L2_Th1_F_LegendreModelEllipticTorsion_key


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
theorem _root_.solution (z : ℂ) : wEta (scalePair L c hc) (c * z) = c⁻¹ * wEta L z := by
  have hb0 : L.basis 0 = L.ω₁ := by
    first
      | exact L.basis_zero
      | simp [PeriodPair.basis]
  have hb1 : L.basis 1 = L.ω₂ := by
    first
      | exact L.basis_one
      | simp [PeriodPair.basis]
  have k1 : wEta (scalePair L c hc) (c * L.ω₁) = c⁻¹ * wEta L L.ω₁ := by
    have h := wEta_basis₁ (scalePair L c hc)
    change wEta (scalePair L c hc) (c * L.ω₁) = 2 * wZeta (scalePair L c hc) (c * L.ω₁ / 2) at h
    rw [h, show c * L.ω₁ / 2 = c * (L.ω₁ / 2) by ring, wZeta_scale L c hc, wEta_basis₁ L]
    ring
  have k2 : wEta (scalePair L c hc) (c * L.ω₂) = c⁻¹ * wEta L L.ω₂ := by
    have h := wEta_basis₂ (scalePair L c hc)
    change wEta (scalePair L c hc) (c * L.ω₂) = 2 * wZeta (scalePair L c hc) (c * L.ω₂ / 2) at h
    rw [h, show c * L.ω₂ / 2 = c * (L.ω₂ / 2) by ring, wZeta_scale L c hc, wEta_basis₂ L]
    ring
  have key : (wEta (scalePair L c hc)).comp (LinearMap.mulLeft ℝ c)
      = (LinearMap.mulLeft ℝ c⁻¹).comp (wEta L) := by
    apply L.basis.ext
    intro i
    fin_cases i
    · first
        | (show wEta (scalePair L c hc) (c * L.basis 0) = c⁻¹ * wEta L (L.basis 0)
           rw [hb0]
           exact k1)
        | (simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, Fin.zero_eta, hb0]
           exact k1)
    · first
        | (show wEta (scalePair L c hc) (c * L.basis 1) = c⁻¹ * wEta L (L.basis 1)
           rw [hb1]
           exact k2)
        | (simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, Fin.mk_one, hb1]
           exact k2)
  exact LinearMap.congr_fun key z
end Formalism.L2.Th1.F.Homog
