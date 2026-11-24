-- Prove2me | solution 1 for DyckAlgebra.DyckRepU.theta_eq_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:23:25.963609+00:00
-- url     : https://prove2.me/submissions/434d3cf7-a376-44ea-8c59-84ca2d5b2f9f

import Definitions.Def_RequestProject_Aqt_PreserveKernel
import Definitions.Def_RequestProject_Aqt_DGamma

set_option autoImplicit true
open DyckAlgebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)
namespace DyckAlgebra.DyckRepU
theorem _root_.solution {L thetaL U Uinv : ρ.carrier}
    (hintertwine : U * L = thetaL * U) (hright : U * Uinv = 1) :
    thetaL = U * L * Uinv := by
  calc thetaL = thetaL * 1 := by rw [mul_one]
    _ = thetaL * (U * Uinv) := by rw [hright]
    _ = thetaL * U * Uinv := by rw [mul_assoc]
    _ = U * L * Uinv := by rw [← hintertwine]
end DyckAlgebra.DyckRepU
