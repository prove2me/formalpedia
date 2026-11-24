-- Prove2me | solution 1 for DyckAlgebra.DyckRepU.w1_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:20:25.697336+00:00
-- url     : https://prove2.me/submissions/e2050554-7719-43bc-9a49-e3cea0056645

import Definitions.Def_RequestProject_Aqt_Theta
import Definitions.Def_RequestProject_Aqt_PreserveKernel
import Theorems.Thm_DyckAlgebra_AqtAction_apply_add
import Theorems.Thm_DyckAlgebra_AqtAction_apply_mul
import Theorems.Thm_DyckAlgebra_AqtAction_apply_one
import Theorems.Thm_DyckAlgebra_DyckRepU_w_comm_yy
attribute [local simp] DyckAlgebra.AqtAction.apply_add
attribute [local simp] DyckAlgebra.AqtAction.apply_mul
attribute [local simp] DyckAlgebra.AqtAction.apply_one



set_option autoImplicit true
open DyckAlgebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)
namespace DyckAlgebra.DyckRepU
theorem _root_.solution : ρ.w 1 - 1 = -(ρ.u • (ρ.w 1 * ρ.yy 1)) := by
  have := ρ.wL 1;
  simp_all +decide [add_mul, DyckRepU.w_comm_yy];
  exact eq_neg_of_add_eq_zero_left ( by rw [ ← this ] ; abel1 )
end DyckAlgebra.DyckRepU
