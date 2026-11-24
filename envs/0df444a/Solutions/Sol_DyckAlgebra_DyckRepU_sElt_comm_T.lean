-- Prove2me | solution 1 for DyckAlgebra.DyckRepU.sElt_comm_T
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:19:59.93783+00:00
-- url     : https://prove2.me/submissions/b6326abb-47f1-4436-b7b0-d9cc84eaf454

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
import Theorems.Thm_DyckAlgebra_DyckRepU_w1_comm_T
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
theorem _root_.solution (j : ℕ) (hj : 2 ≤ j) : ρ.sElt * ρ.T j = ρ.T j * ρ.sElt := by
  unfold DyckRepU.sElt;
  simp +decide only [smul_mul_assoc, mul_smul_comm];
  simp +decide only [mul_assoc, ρ.zTcomm 1 j (by omega)];
  simp +decide only [← mul_assoc, ρ.yTcomm 1 j (by omega)];
  rw [ ρ.w1_comm_T j hj ]
end DyckAlgebra.DyckRepU
