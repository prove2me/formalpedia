-- Prove2me | solution 2 for DyckAlgebra.DyckRepU.thetaDGamma_eq_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:50:56.500119+00:00
-- url     : https://prove2.me/submissions/d2ec36af-5d4d-46a1-ab1e-1f7ff78cc920

import Definitions.Def_RequestProject_Aqt_PreserveKernel
import Definitions.Def_RequestProject_Aqt_DGamma
import Theorems.Thm_DyckAlgebra_DyckRepU_intertwine_dGamma
import Theorems.Thm_DyckAlgebra_DyckRepU_theta_eq_conjugate

set_option autoImplicit true
open DyckAlgebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)
namespace DyckAlgebra.DyckRepU
theorem _root_.solution (γ : List ℕ) (U Uinv : ρ.carrier)
    (hm : U * ρ.dm = ρ.dm * U)
    (hy : U * ρ.yy 1 = ρ.Θy1 * U)
    (hz : U * ρ.zz 1 = ρ.Θz1 * U)
    (hp : U * ρ.dp = ρ.Θdp * U)
    (hright : U * Uinv = 1) :
    ρ.thetaDGamma γ = U * ρ.dGamma γ * Uinv := by
  apply ρ.theta_eq_conjugate
  · exact ρ.intertwine_dGamma U hm hy hz hp γ
  · exact hright
end DyckAlgebra.DyckRepU
