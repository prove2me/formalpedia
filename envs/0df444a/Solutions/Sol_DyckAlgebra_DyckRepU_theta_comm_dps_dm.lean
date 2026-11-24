-- Prove2me | solution 1 for DyckAlgebra.DyckRepU.theta_comm_dps_dm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:21:43.565952+00:00
-- url     : https://prove2.me/submissions/18a59c09-7b4e-46ea-a47b-83f5a605dc9a

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
import Theorems.Thm_DyckAlgebra_DyckRepU_minv_comm_dm

set_option autoImplicit true
open DyckAlgebra
open scoped BigOperators
universe v
attribute [instance] ThetaData.ring ThetaData.algebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)
namespace DyckAlgebra.DyckRepU
theorem _root_.solution :
    ρ.Θdps * ρ.dm - ρ.dm * ρ.Θdps =
      ρ.minv * (ρ.dps * ρ.dm - ρ.dm * ρ.dps) := by
  unfold Θdps
  rw [mul_assoc, ← mul_assoc ρ.dm, ← ρ.minv_comm_dm, mul_assoc]
  noncomm_ring
end DyckAlgebra.DyckRepU
