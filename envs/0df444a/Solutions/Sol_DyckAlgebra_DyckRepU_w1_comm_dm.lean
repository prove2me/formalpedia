-- Prove2me | solution 1 for DyckAlgebra.DyckRepU.w1_comm_dm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:18:32.184262+00:00
-- url     : https://prove2.me/submissions/e466377a-af41-4304-865f-9e9d5d445c32

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
import Theorems.Thm_DyckAlgebra_AqtAction_apply_add
import Theorems.Thm_DyckAlgebra_AqtAction_apply_mul
import Theorems.Thm_DyckAlgebra_AqtAction_apply_one
attribute [local simp] DyckAlgebra.AqtAction.apply_add
attribute [local simp] DyckAlgebra.AqtAction.apply_mul
attribute [local simp] DyckAlgebra.AqtAction.apply_one



set_option autoImplicit true
open DyckAlgebra
open scoped BigOperators
universe v
attribute [instance] ThetaData.ring ThetaData.algebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)
namespace DyckAlgebra.DyckRepU
theorem _root_.solution : ρ.w 1 * ρ.dm = ρ.dm * ρ.w 1 := by
  have hy : (1 + ρ.u • ρ.yy 1) * ρ.dm = ρ.dm * (1 + ρ.u • ρ.yy 1) := by
    simp [add_mul, mul_add, ρ.ydm 1]
  calc
    ρ.w 1 * ρ.dm = ρ.w 1 * ρ.dm * ((1 + ρ.u • ρ.yy 1) * ρ.w 1) := by rw [ρ.wL 1, mul_one]
    _ = ρ.w 1 * (ρ.dm * (1 + ρ.u • ρ.yy 1)) * ρ.w 1 := by simp only [mul_assoc]
    _ = ρ.w 1 * ((1 + ρ.u • ρ.yy 1) * ρ.dm) * ρ.w 1 := by rw [hy]
    _ = (ρ.w 1 * (1 + ρ.u • ρ.yy 1)) * ρ.dm * ρ.w 1 := by simp only [mul_assoc]
    _ = ρ.dm * ρ.w 1 := by rw [ρ.wR 1, one_mul]
end DyckAlgebra.DyckRepU
