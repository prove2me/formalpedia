-- Prove2me | solution 1 for Formalism.L2.Th1.A.Rr.wpPrimeInZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:23:52.356846+00:00
-- url     : https://prove2.me/submissions/4508a42c-239f-4ae7-8761-4d12e1ed0b0f

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementR
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowDouble
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_DifferenceLinearCoeff
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_WeierstrassPPrimeUnit
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_add
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_neg
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_ofNat
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_pow
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_Plus_toL_X_mul
import Theorems.Thm_Formalism_L2_Th1_A_Plus_uPow_neg_three
import Theorems.Thm_Formalism_L2_Th1_A_Two_exp_mul_inv
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_uPow_neg_three
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
import Theorems.Thm_Formalism_L2_Th1_A_toL_injective
import Theorems.Thm_Formalism_L2_Th1_A_wpODE
import Theorems.Thm_Formalism_L2_Th1_A_wpPrimeShape
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.IsDer.toDerivation_apply
attribute [local simp] Formalism.L2.Th1.A.dLDR_apply
attribute [local simp] Formalism.L2.Th1.A.dLD_apply



set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.Rr
variable {K : Type u} [Field K] [CharZero K] (W : WeierstrassCurve K)
namespace Formalism.L2.Th1.A.Rr
theorem _root_.solution : expSer W ^ 3 * (-2 + X ^ 3 * derivative K (wpReg W))
    = X ^ 3 * (-2 * (xS W).subst (expSer W) + C W.a₁ * expSer W * (xS W).subst (expSer W)
        + C W.a₃ * expSer W ^ 3) := by
  have h1 := (wpODE K W).1
  have h2 := (wpPrimeShape K W).1
  have hq := Two.exp_mul_inv W
  have hz : (toL X : LaurentSeries K) * uPow (-1) = 1 := Plus.toL_X_mul
  have hy : (yS W).subst (expSer W) = -(xS W).subst (expSer W) := by
    rw [yS, ← coe_substAlgHom (Two.he W), map_neg]
  rw [h2, xZ, yZ, hy, Plus.uPow_neg_three] at h1
  apply toL_injective
  simp only [map_mul, map_add, map_neg, map_pow, map_ofNat, toL_C] at h1 ⊢
  generalize toL ((xS W).subst (expSer W)) = xs at h1 ⊢
  generalize toL (derivative K (wpReg W)) = P at h1 ⊢
  generalize (toL (expSer W))⁻¹ = q at h1 hq ⊢
  generalize toL (expSer W) = E at hq ⊢
  generalize (uPow (-1) : LaurentSeries K) = zi at h1 hz
  generalize (toL X : LaurentSeries K) = Z at hz ⊢
  linear_combination E ^ 3 * Z ^ 3 * h1 + 2 * E ^ 3 * ((Z * zi) ^ 2 + Z * zi + 1) * hz
    - Z ^ 3 * (2 * xs * ((E * q) ^ 2 + E * q + 1) - HahnSeries.C W.a₁ * E * xs * (E * q + 1)) * hq
end Formalism.L2.Th1.A.Rr
