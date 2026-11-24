-- Prove2me | solution 1 for DyckAlgebra.DyckRepU.thetaYY_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:49:23.467881+00:00
-- url     : https://prove2.me/submissions/ac4dec29-dd81-48ac-8ca1-89e2387ee2a4

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
import Theorems.Thm_DyckAlgebra_DyckRepU_theta_comm_dp_dm
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
    thetaYY q ρ.level ρ.Tinv ρ.T ρ.Θdp ρ.dm 1 = ρ.Θy1 := by
  simp only [thetaYY, Θy1, ThetaData.yy]
  rw [ρ.theta_comm_dp_dm]
  simp only [mul_assoc, mul_smul_comm]
end DyckAlgebra.DyckRepU
