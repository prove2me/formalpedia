-- Prove2me | solution 1 for Formalism.L2.Th1.A.chartFlowToFlow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:20:23.795729+00:00
-- url     : https://prove2.me/submissions/a5a3aa82-fe07-4f86-b0fa-764b8c6301e1

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementF
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_neg
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_of_mul_eq_one
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.IsDer.toDerivation_apply

set_option autoImplicit false
universe u
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
namespace Formalism.L2.Th1.A
theorem _root_.solution : FlowOfUW.{u} := by
  intro A _ W D u w v h hF hvw
  obtain ⟨hW, hDu, hDw⟩ := hF
  unfold WEq at hW
  have hDv : D v = -v ^ 2 * fuAt W u w := by rw [h.map_of_mul_eq_one hvw, hDw]
  refine ⟨?_, ?_, ?_⟩
  · rw [WeierstrassCurve.Affine.equation_iff]
    linear_combination ((-1) * v^2 + (1) * W.a₁ * u * v^2 + (1) * W.a₃ * v + (1) * W.a₃ * w * v^2 + (1) * W.a₂ * u^2 * v^2 + (1) * W.a₄ * u * v + (1) * W.a₄ * u * w * v^2 + (1) * W.a₆ + (1) * W.a₆ * w * v + (1) * W.a₆ * w^2 * v^2) * hvw + ((1) * v^3) * hW
  · rw [h.map_mul, hDv, hDu]
    simp only [fwAt, fuAt]
    linear_combination ((-3) * v + (2) * W.a₁ * u * v + (1) * W.a₂ * u^2 * v + (3) * W.a₃ * w * v + (2) * W.a₄ * u * w * v + (3) * W.a₆ * w^2 * v + (1) * W.a₃) * hvw + ((3) * v^2) * hW
  · rw [h.map_neg, hDv]
    simp only [fuAt]
    linear_combination ((2) * W.a₂ * u * v + (1) * W.a₄ + (1) * W.a₄ * w * v + (1) * W.a₁ * v) * hvw
end Formalism.L2.Th1.A
