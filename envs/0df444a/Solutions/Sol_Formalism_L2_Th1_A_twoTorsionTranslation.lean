-- Prove2me | solution 1 for Formalism.L2.Th1.A.twoTorsionTranslation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:46:53.092044+00:00
-- url     : https://prove2.me/submissions/70994145-c570-4969-9033-789fcffb3616

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementF
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowTwo
import Theorems.Thm_Formalism_L2_Th1_A_QuadraticFlow_der_add
import Theorems.Thm_Formalism_L2_Th1_A_QuadraticFlow_der_mul
import Theorems.Thm_Formalism_L2_Th1_A_QuadraticFlow_der_neg
import Theorems.Thm_Formalism_L2_Th1_A_QuadraticFlow_der_sub
import Theorems.Thm_Formalism_L2_Th1_A_QuadraticFlow_der_ofNat
import Theorems.Thm_Formalism_L2_Th1_A_QuadraticFlow_der_sq
import Theorems.Thm_Formalism_L2_Th1_A_QuadraticFlow_der_inv

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
theorem _root_.solution : FlowTwoTorsion.{u} := by
  intro A _ W D x y xT yT t hD hC hF hT hDxT hDyT h2 ht
  obtain ⟨hE, hDx, hDy⟩ := hF
  obtain ⟨ha1, ha2, ha3, ha4, ha6⟩ := hC
  rw [WeierstrassCurve.Affine.equation_iff] at hE hT
  have hDt : D t = -t ^ 2 * (2 * y + W.a₁ * x + W.a₃) := by
    rw [der_inv hD ht, der_sub hD, hDxT, sub_zero, hDx]
  refine ⟨?_, ?_, ?_⟩
  · simp only [WeierstrassCurve.Affine.addX]
    linear_combination t ^ 2 * hE - t ^ 2 * hT - t ^ 2 * (y - yT) * h2 +
      ((3 * xT + (x - xT) + W.a₂) + t * ((x ^ 2 + x * xT + xT ^ 2 + W.a₂ * (x + xT) + W.a₄) - W.a₁ * yT) - W.a₁ * (y - yT) * t) * ht
  · rw [hDt]
    simp only [WeierstrassCurve.b₂]
    linear_combination 4 * t ^ 4 * hE - 4 * t ^ 4 * hT + t ^ 4 * ((2 * yT + W.a₁ * xT + W.a₃) + 2 * W.a₁ * (x - xT)) * h2 +
      (4 * (3 * xT ^ 2 + 2 * W.a₂ * xT + W.a₄ - W.a₁ * yT) * t ^ 3 + (12 * xT + (W.a₁ ^ 2 + 4 * W.a₂)) * t ^ 2 * (2 + (t * (x - xT) - 1)) + 4 * t * (3 + 3 * (t * (x - xT) - 1) + (t * (x - xT) - 1) ^ 2)) * ht
  · rw [hDt]
    simp only [der_neg hD, der_mul hD, der_add hD, der_sq hD, der_ofNat hD, hDx, hDy, hDt, ha1, ha3,
      WeierstrassCurve.b₂]
    linear_combination 8 * t ^ 3 * hE - 8 * t ^ 3 * hT +
      (2 * t ^ 3 * ((2 * yT + W.a₁ * xT + W.a₃) + 2 * W.a₁ * (x - xT)) - W.a₁ * t ^ 2) * h2 +
      (8 * (3 * xT ^ 2 + 2 * W.a₂ * xT + W.a₄ - W.a₁ * yT) * t ^ 2 + (12 * xT + (W.a₁ ^ 2 + 4 * W.a₂)) * t * (3 + 2 * (t * (x - xT) - 1)) + 12 + 18 * (t * (x - xT) - 1) + 8 * (t * (x - xT) - 1) ^ 2) * ht
end Formalism.L2.Th1.A
