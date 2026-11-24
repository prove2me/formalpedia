-- Prove2me | solution 1 for DyckAlgebra.DyckRepU.theta_z1_dp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:21:50.254389+00:00
-- url     : https://prove2.me/submissions/94ca3480-c0f3-4a2a-8511-ecb65c684dbd

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
import Theorems.Thm_DyckAlgebra_DyckRepU_theta_z1_lhs

set_option autoImplicit true
open DyckAlgebra
open scoped BigOperators
universe v
attribute [instance] ThetaData.ring ThetaData.algebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)
namespace DyckAlgebra.DyckRepU
theorem _root_.solution : ρ.Θz1 * ρ.Θdp = ρ.w 1 * ρ.zz 1 * ρ.dp := by
  rw [DyckRepU.Θz1, DyckRepU.Θdp]
  rw [← mul_assoc, ρ.theta_z1_lhs, mul_assoc]
end DyckAlgebra.DyckRepU
