-- Prove2me | solution 1 for DyckAlgebra.DyckRepU.theta_y1_rhs_key
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:20:15.059109+00:00
-- url     : https://prove2.me/submissions/b1825aae-02e2-4da9-981f-b798366c83a1

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
theorem _root_.solution :
    (1 - ρ.sElt) * ρ.yy 1 = ρ.w 1 * ρ.yy 1 * (1 + ρ.sStarElt) := by
  simp_all +decide [DyckRepU.sElt, DyckRepU.sStarElt];
  have := ρ.wR 1; simp_all +decide [mul_assoc, mul_add, sub_mul, mul_sub] ;
  replace this := congr_arg ( · * ρ.yy 1 ) this ; simp_all +decide [mul_assoc, add_mul];
  grind
end DyckAlgebra.DyckRepU
