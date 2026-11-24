-- Prove2me | solution 1 for DyckAlgebra.DyckRepU.s2_mul_left_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:50:40.533804+00:00
-- url     : https://prove2.me/submissions/cd3538ba-a070-47f9-99e1-fbaae47405c8

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
theorem _root_.solution : (ρ.minv * (1 + ρ.u • ρ.yy 1)) * (1 - ρ.s2Elt) = 1 := by
  have := ρ.sStar_factor;
  convert ρ.mR using 1;
  rw [ mul_assoc, ← this ] ; simp +decide [ DyckRepU.sStarElt ]
end DyckAlgebra.DyckRepU
