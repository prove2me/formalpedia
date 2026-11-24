-- Prove2me | solution 1 for Formalism.L2.Th1.F.jInvScale_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:21:10.600292+00:00
-- url     : https://prove2.me/submissions/544cdd96-d97d-4ca7-a41f-12bf73745557

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstIsogeny
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HasCMByIsogenyOf

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
theorem _root_.solution (h : Homogeneity) : JInvScale := by
  intro L c hc
  obtain ⟨-, -, -, -, -, -, -, -, -, hg2, hg3⟩ := h L c hc
  simp only [Formalism.L2.Th1.CM.jInv, hg2, hg3]
  have hc12 : (c ^ 12)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hc)
  have e1 : ((c ^ 4)⁻¹ * L.g₂) ^ 3 = (c ^ 12)⁻¹ * L.g₂ ^ 3 := by ring
  have e2 : ((c ^ 6)⁻¹ * L.g₃) ^ 2 = (c ^ 12)⁻¹ * L.g₃ ^ 2 := by ring
  rw [e1, e2, show (1728 : ℂ) * ((c ^ 12)⁻¹ * L.g₂ ^ 3) = (c ^ 12)⁻¹ * (1728 * L.g₂ ^ 3) by ring,
    show (c ^ 12)⁻¹ * L.g₂ ^ 3 - 27 * ((c ^ 12)⁻¹ * L.g₃ ^ 2)
      = (c ^ 12)⁻¹ * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) by ring,
    mul_div_mul_left _ _ hc12]
end Formalism.L2.Th1.F
