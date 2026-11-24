-- Prove2me | solution 1 for DyckAlgebra.Theta.y_mul_one_add_sStar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:49:19.834581+00:00
-- url     : https://prove2.me/submissions/51e26f02-e18b-4290-97a0-2c5e13842b85

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
open DyckAlgebra.Theta
variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
namespace DyckAlgebra.Theta
theorem _root_.solution (u : 𝕜) (w y z : A)
    (hwL : (1 + u • y) * w = 1) (hyz : y * z = z * y) :
    y * (1 + sStar u y z) = (1 + u • y) * (1 - s u w y z) * y := by
  unfold s sStar
  simp_all +decide [mul_sub, sub_mul, ← mul_assoc]
  simp +decide [mul_add, add_mul, mul_sub, mul_assoc]
  simp +decide only [← mul_assoc, smul_sub]
  rw [← hyz, add_sub_assoc]
end DyckAlgebra.Theta
