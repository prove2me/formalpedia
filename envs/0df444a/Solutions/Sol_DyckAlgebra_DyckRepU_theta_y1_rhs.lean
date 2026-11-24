-- Prove2me | solution 1 for DyckAlgebra.DyckRepU.theta_y1_rhs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:21:54.922303+00:00
-- url     : https://prove2.me/submissions/69a0137a-a390-48ca-a974-d890f432b276

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
import Theorems.Thm_DyckAlgebra_DyckRepU_theta_y1_rhs_key

set_option autoImplicit true
open DyckAlgebra
open scoped BigOperators
universe v
attribute [instance] ThetaData.ring ThetaData.algebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)
namespace DyckAlgebra.DyckRepU
theorem _root_.solution : (1 - ρ.sElt) * ρ.yy 1 * ρ.minv = ρ.w 1 * ρ.yy 1 := by
  have hmL : (1 + ρ.sStarElt) * ρ.minv = 1 := ρ.mL
  calc (1 - ρ.sElt) * ρ.yy 1 * ρ.minv
      = (ρ.w 1 * ρ.yy 1 * (1 + ρ.sStarElt)) * ρ.minv := by rw [ρ.theta_y1_rhs_key]
    _ = ρ.w 1 * ρ.yy 1 * ((1 + ρ.sStarElt) * ρ.minv) := by rw [mul_assoc]
    _ = ρ.w 1 * ρ.yy 1 := by rw [hmL, mul_one]
end DyckAlgebra.DyckRepU
