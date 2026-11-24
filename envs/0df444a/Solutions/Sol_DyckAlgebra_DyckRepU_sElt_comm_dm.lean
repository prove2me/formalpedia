-- Prove2me | solution 1 for DyckAlgebra.DyckRepU.sElt_comm_dm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:20:17.466496+00:00
-- url     : https://prove2.me/submissions/e5d38763-78b8-4a82-aaa2-9869c4863d49

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
import Theorems.Thm_DyckAlgebra_DyckRepU_w1_comm_dm
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
theorem _root_.solution : ρ.sElt * ρ.dm = ρ.dm * ρ.sElt := by
  unfold sElt
  simp only [smul_mul_assoc, mul_smul_comm]
  congr 1
  calc
    ρ.w 1 * ρ.yy 1 * ρ.zz 1 * ρ.dm
        = ρ.w 1 * ρ.yy 1 * (ρ.zz 1 * ρ.dm) := by simp only [mul_assoc]
    _ = ρ.w 1 * ρ.yy 1 * (ρ.dm * ρ.zz 1) := by rw [ρ.zdm 1]
    _ = ρ.w 1 * (ρ.yy 1 * ρ.dm) * ρ.zz 1 := by simp only [mul_assoc]
    _ = ρ.w 1 * (ρ.dm * ρ.yy 1) * ρ.zz 1 := by rw [ρ.ydm 1]
    _ = (ρ.w 1 * ρ.dm) * ρ.yy 1 * ρ.zz 1 := by simp only [mul_assoc]
    _ = (ρ.dm * ρ.w 1) * ρ.yy 1 * ρ.zz 1 := by rw [ρ.w1_comm_dm]
    _ = ρ.dm * (ρ.w 1 * ρ.yy 1 * ρ.zz 1) := by simp only [mul_assoc]
end DyckAlgebra.DyckRepU
