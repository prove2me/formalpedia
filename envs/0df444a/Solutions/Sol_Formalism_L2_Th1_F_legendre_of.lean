-- Prove2me | solution 1 for Formalism.L2.Th1.F.legendre_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:44:05.257135+00:00
-- url     : https://prove2.me/submissions/026e49f2-b18c-4e35-b679-1850cf729542

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Legendre
import Theorems.Thm_Formalism_L2_Th1_F_LegendreModelEllipticTorsion_key
import Theorems.Thm_Formalism_L2_Th1_F_LegendreModelEllipticTorsion_im_pos_of_not

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open UpperHalfPlane hiding I
open EisensteinSeries Complex SummationFilter ModularGroup
open scoped Real
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
namespace Formalism.L2.Th1.F
theorem _root_.solution (h : EtaEisenstein) : Legendre := by
  intro L
  obtain ⟨h1, h2⟩ := h L
  rw [h1, h2]
  split_ifs with hp
  · rw [one_mul]
    exact LegendreModelEllipticTorsion.key L.ω₁ L.ω₂ hp
  · have hp' := LegendreModelEllipticTorsion.im_pos_of_not L hp
    have k := LegendreModelEllipticTorsion.key L.ω₂ L.ω₁ hp'
    have e1 : (∑' n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) * L.ω₂ + (n : ℂ) * L.ω₁) ^ 2)
        = ∑' m : ℤ, ∑' n : ℤ, 1 / ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) ^ 2 := by
      congr 1; funext a; congr 1; funext b; ring
    have e2 : (∑' m : ℤ, ∑' n : ℤ, 1 / ((m : ℂ) * L.ω₂ + (n : ℂ) * L.ω₁) ^ 2)
        = ∑' n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) ^ 2 := by
      congr 1; funext a; congr 1; funext b; ring
    rw [e1, e2] at k
    linear_combination -k
end Formalism.L2.Th1.F
