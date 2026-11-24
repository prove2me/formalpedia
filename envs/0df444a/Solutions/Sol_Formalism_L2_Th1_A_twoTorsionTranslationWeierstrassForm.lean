-- Prove2me | solution 1 for Formalism.L2.Th1.A.twoTorsionTranslationWeierstrassForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:06:02.811775+00:00
-- url     : https://prove2.me/submissions/258255d5-b94d-472e-ba3b-26aff6b6dd4e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementF
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowTwo
import Theorems.Thm_Formalism_L2_Th1_A_QuadraticFlow_cancel_unit
import Theorems.Thm_Formalism_L2_Th1_A_QuadraticFlow_unit_four
import Theorems.Thm_Formalism_L2_Th1_A_QuadraticFlow_unit_twelve
import Theorems.Thm_Formalism_L2_Th1_A_QuadraticFlow_weierstrassSubstitution_unit_fact
import Theorems.Thm_Formalism_L2_Th1_A_twoTorsionTranslation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open QuadraticFlow
namespace Formalism.L2.Th1.A
theorem _root_.solution : FlowTwoTorsionWp.{u} := by
  intro A _ W D x y xT yT t c g2 g3 kap hD hC hF hT hDxT hDyT h2 ht h6 hc hg2 hg3 hk
  have H1 := twoTorsionTranslation A W D x y xT yT t hD hC hF hT hDxT hDyT h2 ht
  rw [WeierstrassCurve.Affine.equation_iff] at hT
  have hkap : kap = (3 * xT ^ 2 + 2 * W.a₂ * xT + W.a₄ - W.a₁ * yT) := by
    apply cancel_unit ((unit_four h6).mul (unit_twelve h6))
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.c₄] at hc hg2
    linear_combination 12 * hk + (24 * xT + 12 * c + (W.a₁ ^ 2 + 4 * W.a₂)) * hc - hg2 + 24 * W.a₁ * h2
  have ha : 4 * (xT + c) ^ 3 - g2 * (xT + c) - g3 = 0 := by
    apply cancel_unit (weierstrassSubstitution_unit_fact h6)
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.c₄,
      WeierstrassCurve.c₆] at hc hg2 hg3
    linear_combination ((12 * xT + 12 * c) ^ 2 + (12 * xT + 12 * c) * (12 * xT + (W.a₁ ^ 2 + 4 * W.a₂)) + (12 * xT + (W.a₁ ^ 2 + 4 * W.a₂)) ^ 2 - 3 * ((W.a₁ ^ 2 + 4 * W.a₂) ^ 2 - 24 * (2 * W.a₄ + W.a₁ * W.a₃))) * hc - 36 * (xT + c) * hg2 -
      2 * hg3 + 432 * (2 * yT + W.a₁ * xT + W.a₃) * h2 - 1728 * hT
  have hd : D t ^ 2 = 4 * t * (1 + 3 * (xT + c) * t + kap * t ^ 2) := by
    linear_combination H1.2.1 - t ^ 2 * hc - 4 * t ^ 3 * hkap
  refine ⟨ha, hkap, ?_, hd, ?_⟩
  · rw [H1.1, hkap]
    ring
  · intro e2 e3 hs he
    linear_combination hd + (4 * t ^ 2 + 8 * (xT + c) * t ^ 3) * hs + t ^ 3 * hk - t ^ 3 * he
end Formalism.L2.Th1.A
