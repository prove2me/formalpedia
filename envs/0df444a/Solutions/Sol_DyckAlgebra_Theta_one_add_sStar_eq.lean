-- Prove2me | solution 1 for DyckAlgebra.Theta.one_add_sStar_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:18:25.257708+00:00
-- url     : https://prove2.me/submissions/ea7572d9-4f66-4cf0-a3ff-e76789d648d9

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
    (hwL : (1 + u • y) * w = 1) :
    1 + sStar u y z = (1 + u • y) * (1 - u • (w * z * y)) := by
  simp +decide [sStar, mul_sub, sub_mul];
  simp +decide [ ← mul_assoc, hwL ];
  rw [ smul_sub, add_sub_assoc ]
end DyckAlgebra.Theta
