-- Prove2me | solution 1 for Formalism.L2.Th1.A.Two.wpInZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:42:47.690828+00:00
-- url     : https://prove2.me/submissions/62326b60-8fdb-48f6-84a0-ab18249a8176

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_TwoTorsionIntegral
import Theorems.Thm_Formalism_L2_Th1_A_Two_toL_exp_ne
import Theorems.Thm_Formalism_L2_Th1_A_Two_uPow_mul_sq
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_add
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_one
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_pow
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
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
open Two
open Formalism.L2.Th1.A.Two
variable {K : Type u} [Field K] [CharZero K] (W : WeierstrassCurve K)
namespace Formalism.L2.Th1.A.Two
theorem _root_.solution (hS : WpShape.{u}) : expSer W ^ 2 * (1 + X ^ 2 * wpReg W)
    = X ^ 2 * ((xS W).subst (expSer W) + C (W.b₂ / 12) * expSer W ^ 2) := by
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := K)
  have hw := (hS K W).1
  unfold wpL xZ at hw
  have hP : (uPow (-2) : LaurentSeries K) * toL X ^ 2 = 1 := uPow_mul_sq
  have hE1 : toL (expSer W) * (toL (expSer W))⁻¹ = 1 := mul_inv_cancel₀ (toL_exp_ne W)
  simp only [map_mul, map_pow, map_add, map_one, HahnSeries.ofPowerSeries_C]
  linear_combination (-(toL X ^ 2 * toL (expSer W) ^ 2)) * hw + (-(toL (expSer W) ^ 2)) * hP
    + (toL X ^ 2 * toL ((xS W).subst (expSer W)) * (toL (expSer W) * (toL (expSer W))⁻¹ + 1)) * hE1
end Formalism.L2.Th1.A.Two
