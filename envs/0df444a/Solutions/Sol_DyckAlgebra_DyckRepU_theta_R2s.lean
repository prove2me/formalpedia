-- Prove2me | solution 1 for DyckAlgebra.DyckRepU.theta_R2s
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:50:13.022589+00:00
-- url     : https://prove2.me/submissions/a59fa2de-31c4-42bb-adc6-7ae029624900

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
import Theorems.Thm_DyckAlgebra_DyckRepU_minv_comm_Tinv

set_option autoImplicit true
open DyckAlgebra
open scoped BigOperators
universe v
attribute [instance] ThetaData.ring ThetaData.algebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)
namespace DyckAlgebra.DyckRepU
theorem _root_.solution (i : ℕ) (h : 1 ≤ i) : ρ.Θdps * ρ.Tinv i = ρ.Tinv (i+1) * ρ.Θdps := by
  rw [ DyckRepU.Θdps, mul_assoc, ρ.R2s i h, ← mul_assoc, ρ.minv_comm_Tinv ];
  · rw [ mul_assoc ];
  · linarith
end DyckAlgebra.DyckRepU
