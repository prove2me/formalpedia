-- Prove2me | solution 1 for DyckAlgebra.DyckRepU.s2_mul_minv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:21:47.708785+00:00
-- url     : https://prove2.me/submissions/63e47181-5b21-4e03-be95-5e161cfd1bd7

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
import Theorems.Thm_DyckAlgebra_DyckRepU_sStar_factor
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
theorem _root_.solution : (1 - ρ.s2Elt) * ρ.minv = ρ.w 1 := by
  have h_mul : ρ.w 1 * ((1 + ρ.u • ρ.yy 1) * (1 - ρ.s2Elt)) * ρ.minv = ρ.w 1 * 1 := by
    rw [ ← ρ.sStar_factor, mul_assoc ];
    exact congr_arg _ ρ.mL;
  convert h_mul using 1 <;> simp +decide [ ← mul_assoc, ρ.wR ]
end DyckAlgebra.DyckRepU
