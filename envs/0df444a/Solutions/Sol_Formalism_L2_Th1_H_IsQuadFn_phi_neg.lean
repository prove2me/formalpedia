-- Prove2me | solution 1 for Formalism.L2.Th1.H.IsQuadFn.phi_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:39:06.090824+00:00
-- url     : https://prove2.me/submissions/2756deb6-f1dc-4068-90fd-319fbdf01f78

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GaussSumEighthPower
import Theorems.Thm_Formalism_L2_Th1_H_IsQuadFn_phi_zero
import Theorems.Thm_Formalism_L2_Th1_H_IsQuadFn_b_neg_right
import Theorems.Thm_Formalism_L2_Th1_H_IsQuadFn_b_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
open Formalism.L2.Th1.H.IsQuadFn
variable {M : Type*} [AddCommGroup M] {φ : M → ℂ} {b : M → M → ℂ}
namespace Formalism.L2.Th1.H.IsQuadFn
theorem _root_.solution (h : IsQuadFn φ b) (x : M) : φ (-x) = φ x := by
  have hx := h.ne x
  have h1 := h.add x (-x)
  rw [show x + -x = (0 : M) by simp, h.phi_zero, h.b_neg_right, h.b_self] at h1
  calc φ (-x) = φ (-x) * (φ x ^ 2 * (φ x ^ 2)⁻¹) := by
        rw [mul_inv_cancel₀ (pow_ne_zero 2 hx), mul_one]
    _ = φ x * φ (-x) * (φ x ^ 2)⁻¹ * φ x := by ring
    _ = φ x := by rw [← h1, one_mul]
end Formalism.L2.Th1.H.IsQuadFn
