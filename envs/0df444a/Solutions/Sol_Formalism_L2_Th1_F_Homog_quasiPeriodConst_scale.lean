-- Prove2me | solution 1 for Formalism.L2.Th1.F.Homog.quasiPeriodConst_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:09:34.199008+00:00
-- url     : https://prove2.me/submissions/b69a3184-639c-4c5a-8be2-155af181f217

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_LatticeOnly
import Theorems.Thm_Formalism_L2_Th1_F_Homog_wEta_scale

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
theorem _root_.solution : s2 (scalePair L c hc) = (c ^ 2)⁻¹ * s2 L := by
  have hcc : conj c ≠ 0 := (map_ne_zero _).mpr hc
  simp only [s2]
  change (wEta (scalePair L c hc) (c * L.ω₁) * conj (c * L.ω₂)
      - wEta (scalePair L c hc) (c * L.ω₂) * conj (c * L.ω₁))
      / (c * L.ω₁ * conj (c * L.ω₂) - c * L.ω₂ * conj (c * L.ω₁)) = _
  rw [wEta_scale L c hc, wEta_scale L c hc, map_mul, map_mul]
  rw [show c⁻¹ * wEta L L.ω₁ * (conj c * conj L.ω₂) - c⁻¹ * wEta L L.ω₂ * (conj c * conj L.ω₁)
      = (c⁻¹ * conj c) * (wEta L L.ω₁ * conj L.ω₂ - wEta L L.ω₂ * conj L.ω₁) by ring,
    show c * L.ω₁ * (conj c * conj L.ω₂) - c * L.ω₂ * (conj c * conj L.ω₁)
      = (c * conj c) * (L.ω₁ * conj L.ω₂ - L.ω₂ * conj L.ω₁) by ring,
    mul_div_mul_comm]
  congr 1
  first
    | (field_simp
       done)
    | (field_simp
       ring)
    | (rw [div_eq_iff (mul_ne_zero hc hcc)]
       field_simp
       ring)
end Formalism.L2.Th1.F.Homog
