-- Prove2me | solution 1 for DyckAlgebra.DyckRepU.theta_Q2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:23:39.320811+00:00
-- url     : https://prove2.me/submissions/063d826a-caa0-4cc0-8c9a-00b8c930ca49

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
import Theorems.Thm_DyckAlgebra_DyckRepU_theta_z1_lhs
import Theorems.Thm_DyckAlgebra_DyckRepU_theta_y1_rhs
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
theorem _root_.solution : ρ.Θz1 * ρ.Θdp = cQ2 • (ρ.Θy1 * ρ.Θdps) := by
  convert congr_arg ( fun x : ρ.carrier => x * ρ.dp ) ρ.theta_z1_lhs using 1;
  · simp +decide [ mul_assoc, DyckRepU.Θz1, DyckRepU.Θdp ];
  · convert congr_arg ( fun x : ρ.carrier => cQ2 • ( x * ρ.dps ) ) ρ.theta_y1_rhs using 1;
    · simp +decide [ mul_assoc, DyckRepU.Θy1, DyckRepU.Θdps ];
    · convert congr_arg ( fun x : ρ.carrier => ρ.w 1 * x ) ρ.Q2 using 1 <;> simp +decide [ mul_assoc ]
end DyckAlgebra.DyckRepU
