-- Prove2me | solution 1 for DyckAlgebra.DyckRepU.theta_I2_operator_scalar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:24:50.850638+00:00
-- url     : https://prove2.me/submissions/286e6a20-53d5-454c-9d59-a69efe269135

import Definitions.Def_RequestProject_Aqt_Theta
import Definitions.Def_RequestProject_Aqt_PreserveKernel
import Theorems.Thm_DyckAlgebra_AqtAction_apply_add
import Theorems.Thm_DyckAlgebra_AqtAction_apply_mul
import Theorems.Thm_DyckAlgebra_AqtAction_apply_one
import Theorems.Thm_DyckAlgebra_DyckRepU_theta_y1_dps
import Theorems.Thm_DyckAlgebra_DyckRepU_w1_yy1_one_add
attribute [local simp] DyckAlgebra.AqtAction.apply_add
attribute [local simp] DyckAlgebra.AqtAction.apply_mul
attribute [local simp] DyckAlgebra.AqtAction.apply_one



set_option autoImplicit true
open DyckAlgebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)
namespace DyckAlgebra.DyckRepU
theorem _root_.solution (a : 𝕜) (hcQ2 : cQ2 = -a) :
    ρ.Θdp + a • (ρ.Θy1 * ρ.Θdps) = ρ.dp + a • (ρ.yy 1 * ρ.dps) := by
  unfold DyckRepU.Θdp DyckRepU.Θy1 DyckRepU.Θdps;
  have h_sStar_dp : ρ.u • (ρ.w 1 * ρ.yy 1 * ρ.zz 1) * ρ.dp = -a • (ρ.u • (ρ.w 1 * ρ.yy 1 * ρ.yy 1) * ρ.dps) := by
    have := ρ.Q2; simp_all +decide [ mul_assoc, smul_smul ] ;
    rw [ mul_comm ];
  have h_sStar_dp : (1 - ρ.u • (ρ.w 1 * ρ.yy 1 * ρ.zz 1)) * ρ.dp = ρ.dp - (-a • (ρ.u • (ρ.w 1 * ρ.yy 1 * ρ.yy 1) * ρ.dps)) := by
    rw [ ← h_sStar_dp, sub_mul, one_mul ];
  have h_sStar_dp : (1 - ρ.u • (ρ.w 1 * ρ.yy 1 * ρ.zz 1)) * ρ.yy 1 * (ρ.minv * ρ.dps) = ρ.w 1 * ρ.yy 1 * ρ.dps := by
    simpa [DyckRepU.Θy1, DyckRepU.Θdps, DyckRepU.sElt] using DyckRepU.theta_y1_dps ρ
  have h_sStar_dp : ρ.w 1 * ρ.yy 1 * ρ.dps = ρ.yy 1 * ρ.dps - ρ.u • (ρ.w 1 * ρ.yy 1 * ρ.yy 1) * ρ.dps := by
    have h_sStar_dp : ρ.w 1 * ρ.yy 1 * (1 + ρ.u • ρ.yy 1) * ρ.dps = ρ.yy 1 * ρ.dps := by
      have := ρ.w1_yy1_one_add;
      rw [this];
    simp_all +decide [ mul_add, add_mul, mul_assoc ];
    exact eq_sub_of_add_eq h_sStar_dp;
  simp_all +decide [ DyckRepU.sElt ];
  simp +decide [ add_assoc, smul_sub ]
end DyckAlgebra.DyckRepU
