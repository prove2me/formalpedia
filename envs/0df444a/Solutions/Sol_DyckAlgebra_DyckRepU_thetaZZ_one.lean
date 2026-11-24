-- Prove2me | solution 1 for DyckAlgebra.DyckRepU.thetaZZ_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:49:46.57257+00:00
-- url     : https://prove2.me/submissions/a6d281e5-47a7-4c06-bddf-e29fde15f4bd

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
import Theorems.Thm_DyckAlgebra_DyckRepU_theta_comm_dps_dm
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
    thetaZZ q ρ.t ρ.level ρ.T ρ.Tinv ρ.Θdps ρ.dm 1 = ρ.Θz1 := by
  simp only [thetaZZ, Θz1, ThetaData.zz]
  rw [ρ.theta_comm_dps_dm]
  simp only [mul_assoc, mul_smul_comm]
end DyckAlgebra.DyckRepU
