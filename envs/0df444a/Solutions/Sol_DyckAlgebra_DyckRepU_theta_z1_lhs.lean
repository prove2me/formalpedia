-- Prove2me | solution 1 for DyckAlgebra.DyckRepU.theta_z1_lhs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:20:11.04279+00:00
-- url     : https://prove2.me/submissions/da61f792-3873-4ade-9557-3012c63c06d6

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
import Theorems.Thm_DyckAlgebra_Theta_z_mul_one_sub_s
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
theorem _root_.solution : ρ.minv * ρ.zz 1 * (1 - ρ.sElt) = ρ.w 1 * ρ.zz 1 := by
  have h_comm : ρ.minv * (1 + ρ.sStarElt) = 1 := by
    simpa [DyckRepU.sStarElt] using ρ.mR
  have h_comm : ρ.zz 1 * (1 - ρ.sElt) = (1 + ρ.sStarElt) * ρ.w 1 * ρ.zz 1 := by
    have h := DyckAlgebra.Theta.z_mul_one_sub_s ρ.u (ρ.w 1) (ρ.yy 1) (ρ.zz 1) (ρ.wL 1) (ρ.wR 1)
    have hs : ρ.sStarElt = Theta.sStar ρ.u (ρ.yy 1) (ρ.zz 1) := by
      unfold DyckRepU.sStarElt Theta.sStar
      simp +decide [sub_mul, smul_sub]
    simpa [hs, DyckRepU.sElt, Theta.s] using h
  grind +revert
end DyckAlgebra.DyckRepU
