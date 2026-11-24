-- Prove2me | solution 1 for DyckAlgebra.DyckRepU.sStarElt_comm_Tinv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:21:03.819805+00:00
-- url     : https://prove2.me/submissions/074341ec-1551-407a-b2bf-622c7e60ada7

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
import Theorems.Thm_DyckAlgebra_DyckRepU_yy_comm_Tinv
import Theorems.Thm_DyckAlgebra_DyckRepU_zz_comm_Tinv
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
theorem _root_.solution (j : ℕ) (hj : 2 ≤ j) :
    ρ.sStarElt * ρ.Tinv j = ρ.Tinv j * ρ.sStarElt := by
  unfold DyckRepU.sStarElt;
  simp +decide [mul_sub, sub_mul, mul_assoc];
  simp +decide only [ρ.yy_comm_Tinv 1 j (by omega), ← mul_assoc, ρ.zz_comm_Tinv 1 j (by omega)]
end DyckAlgebra.DyckRepU
