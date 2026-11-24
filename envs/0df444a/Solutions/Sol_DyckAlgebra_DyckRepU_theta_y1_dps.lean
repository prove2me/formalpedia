-- Prove2me | solution 1 for DyckAlgebra.DyckRepU.theta_y1_dps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:23:34.458819+00:00
-- url     : https://prove2.me/submissions/7e0b1b90-e983-40ae-a766-104e3f993ac5

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
import Theorems.Thm_DyckAlgebra_DyckRepU_theta_y1_rhs

set_option autoImplicit true
open DyckAlgebra
open scoped BigOperators
universe v
attribute [instance] ThetaData.ring ThetaData.algebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)
namespace DyckAlgebra.DyckRepU
theorem _root_.solution : ρ.Θy1 * ρ.Θdps = ρ.w 1 * ρ.yy 1 * ρ.dps := by
  rw [DyckRepU.Θy1, DyckRepU.Θdps]
  rw [← mul_assoc, ρ.theta_y1_rhs, mul_assoc]
end DyckAlgebra.DyckRepU
