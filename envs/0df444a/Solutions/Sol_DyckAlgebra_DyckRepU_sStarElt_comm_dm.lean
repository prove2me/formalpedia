-- Prove2me | solution 1 for DyckAlgebra.DyckRepU.sStarElt_comm_dm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:18:40.349101+00:00
-- url     : https://prove2.me/submissions/8373b7a3-b43f-4f35-9716-49c0d35bd900

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
theorem _root_.solution : ρ.sStarElt * ρ.dm = ρ.dm * ρ.sStarElt := by
  unfold sStarElt
  rw [sub_mul, mul_sub]
  simp only [smul_mul_assoc, mul_smul_comm]
  rw [ρ.ydm 1]
  change ρ.u • (ρ.dm * ρ.yy 1) - ρ.u • (ρ.zz 1 * ρ.yy 1 * ρ.dm) =
    ρ.u • (ρ.dm * ρ.yy 1) - ρ.u • (ρ.dm * (ρ.zz 1 * ρ.yy 1))
  have hprod : ρ.zz 1 * ρ.yy 1 * ρ.dm = ρ.dm * (ρ.zz 1 * ρ.yy 1) := by
    calc
      ρ.zz 1 * ρ.yy 1 * ρ.dm = ρ.zz 1 * (ρ.yy 1 * ρ.dm) := by simp only [mul_assoc]
      _ = ρ.zz 1 * (ρ.dm * ρ.yy 1) := by rw [ρ.ydm 1]
      _ = (ρ.zz 1 * ρ.dm) * ρ.yy 1 := by simp only [mul_assoc]
      _ = (ρ.dm * ρ.zz 1) * ρ.yy 1 := by rw [ρ.zdm 1]
      _ = ρ.dm * (ρ.zz 1 * ρ.yy 1) := by simp only [mul_assoc]
  rw [hprod]
end DyckAlgebra.DyckRepU
