-- Prove2me | solution 1 for Formalism.L2.Th1.A.flowWeierstrassForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:30:46.106087+00:00
-- url     : https://prove2.me/submissions/3702d6fd-6d90-43e2-980a-342be3329be1

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementF
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_add
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_ofNat
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_sq
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_flowDifferentialEquation
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
theorem _root_.solution : FlowWp.{u} := by
  intro A _ W D x y c g2 g3 h hC hF hu6 h12c h12g2 h216g3
  obtain ⟨hsq1, hsq2⟩ := flowDifferentialEquation A W D x y h hC hF
  obtain ⟨c1, c2, c3, c4, c6⟩ := hC
  obtain ⟨hE, hDx, hDy⟩ := hF
  obtain ⟨s, hs⟩ := hu6.exists_right_inv
  have hb := congrArg D h12c
  simp only [WeierstrassCurve.b₂, h.map_add, h.map_mul, h.map_sq, h.map_ofNat, c1, c2] at hb
  have h12 : 12 * D c = 0 := by linear_combination hb
  have hDc : D c = 0 := by linear_combination (-(6 * s + 1) * D c) * hs + 3 * s ^ 2 * h12
  have hDxc : D (x + c) = D x := by rw [h.map_add, hDc, add_zero]
  rw [WeierstrassCurve.c₄] at h12g2
  rw [WeierstrassCurve.c₆] at h216g3
  have hb4 : 2 * W.b₄ = 12 * c ^ 2 - g2 := by
    linear_combination (-(6 * s + 1) * (2 * W.b₄ - (12 * c ^ 2 - g2))) * hs + 3 * s ^ 2 * h12g2
      - 3 * s ^ 2 * (12 * c + W.b₂) * h12c
  have hb6 : W.b₆ = -g3 + 4 * c ^ 3 - c * g2 := by
    linear_combination (-(36 * s ^ 2 + 6 * s + 1) * (W.b₆ - (-g3 + 4 * c ^ 3 - c * g2))) * hs
      + s ^ 3 * (h216g3 + (144 * c ^ 2 + 12 * c * W.b₂ + W.b₂ ^ 2 - 36 * W.b₄) * h12c
        + 216 * c * hb4)
  refine ⟨?_, ?_, ?_⟩
  · rw [hDxc, hDx]
  · rw [hDxc]
    linear_combination hsq1 - x ^ 2 * h12c + x * hb4 + hb6
  · rw [hDxc]
    linear_combination 2 * hsq2 - 2 * x * h12c + hb4
end Formalism.L2.Th1.A
