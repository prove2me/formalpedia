-- Prove2me | solution 1 for DyckAlgebra.Theta.z_mul_one_sub_s
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:18:24.64048+00:00
-- url     : https://prove2.me/submissions/617e4416-ef68-4542-902e-b48df2af734b

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
import Theorems.Thm_DyckAlgebra_Theta_w_comm_y
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
    (hwL : (1 + u • y) * w = 1) (hwR : w * (1 + u • y) = 1) :
    z * (1 - s u w y z) = (1 + sStar u y z) * w * z := by
  unfold s sStar
  have hw_comm : w * y = y * w := w_comm_y u w y hwL hwR
  simp_all +decide [mul_assoc, add_mul, mul_add, sub_mul, mul_sub]
  simp_all +decide [← mul_assoc, smul_sub]
  replace hwL := congr_arg (· * z) hwL
  simp_all +decide [mul_assoc, add_mul]
  grind
end DyckAlgebra.Theta
