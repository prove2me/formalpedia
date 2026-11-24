-- Prove2me | solution 1 for DyckAlgebra.DyckRepU.w_comm_yy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:06:00.758317+00:00
-- url     : https://prove2.me/submissions/8123fbe1-d58f-4610-98b1-d698525f8acc

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
import Theorems.Thm_DyckAlgebra_Theta_w_comm_y

set_option autoImplicit true
open DyckAlgebra
open scoped BigOperators
universe v
attribute [instance] ThetaData.ring ThetaData.algebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)
namespace DyckAlgebra.DyckRepU
theorem _root_.solution (i : ℕ) : ρ.w i * ρ.yy i = ρ.yy i * ρ.w i :=
  Theta.w_comm_y ρ.u (ρ.w i) (ρ.yy i) (ρ.wL i) (ρ.wR i)
end DyckAlgebra.DyckRepU
