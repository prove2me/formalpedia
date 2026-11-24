-- Prove2me | solution 1 for DyckAlgebra.DyckRepU.theta_comm_dp_dm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:21:56.633961+00:00
-- url     : https://prove2.me/submissions/e17507d2-20fc-4858-8857-ef0fd108790a

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
import Theorems.Thm_DyckAlgebra_DyckRepU_sElt_comm_dm
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
    ρ.Θdp * ρ.dm - ρ.dm * ρ.Θdp =
      (1 - ρ.sElt) * (ρ.dp * ρ.dm - ρ.dm * ρ.dp) := by
  have hs : (1 - ρ.sElt) * ρ.dm = ρ.dm * (1 - ρ.sElt) := by
    simp [sub_mul, mul_sub, ρ.sElt_comm_dm]
  unfold Θdp
  rw [mul_assoc, ← mul_assoc ρ.dm, ← hs, mul_assoc]
  noncomm_ring
end DyckAlgebra.DyckRepU
