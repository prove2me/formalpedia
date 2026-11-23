-- Prove2me | solution 1 for Formalism.L2.Th1.A.chartFlowNegation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:18.746868+00:00
-- url     : https://prove2.me/submissions/12482241-c600-4c66-8807-d0c6e1b5dffc

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementF
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_add
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_one
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
theorem _root_.solution : FlowNegUW.{u} := by
  intro A _ W D u w r h hC hF hr
  obtain ⟨c1, c2, c3, c4, c6⟩ := hC
  obtain ⟨hW, hDu, hDw⟩ := hF
  unfold WEq at hW
  have hDq : D (-1 + W.a₁ * u + W.a₃ * w) = W.a₁ * fwAt W u w + W.a₃ * fuAt W u w := by
    simp only [h.map_add, h.map_neg, h.map_one, h.map_mul, c1, c3, hDu, hDw]
    ring
  have hDr : D r = -r ^ 2 * (W.a₁ * fwAt W u w + W.a₃ * fuAt W u w) := by
    rw [h.map_of_mul_eq_one hr, hDq]
  refine ⟨?_, ?_, ?_⟩
  · unfold WEq
    linear_combination ((-1) * w * r + (1) * w * r^2) * hr + ((1) * r^3) * hW
  · show -D (u * r) = fwAt W (u * r) (w * r)
    rw [h.map_mul, hDr, hDu]
    simp only [fwAt, fuAt]
    linear_combination ((-1) * W.a₁ * u * r + (-1) * W.a₂ * u^2 * r + (-3) * W.a₃ * w * r + (-2) * W.a₄ * u * w * r + (-3) * W.a₆ * w^2 * r + (1) * 1) * hr + ((-3) * W.a₃ * r^2) * hW
  · show -D (w * r) = fuAt W (u * r) (w * r)
    rw [h.map_mul, hDr, hDw]
    simp only [fwAt, fuAt]
    linear_combination ((3) * u^2 * r + (2) * W.a₁ * w * r + (2) * W.a₂ * u * w * r + (1) * W.a₄ * w^2 * r) * hr + ((3) * W.a₁ * r^2) * hW
end Formalism.L2.Th1.A
