-- Prove2me | solution 1 for DyckAlgebra.DyckRepU.theta_preserve_I1_via_sStar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:25:55.492319+00:00
-- url     : https://prove2.me/submissions/8315da66-4c3e-4d3c-8c18-184efbb24446

import Definitions.Def_RequestProject_Aqt_Theta
import Definitions.Def_RequestProject_Aqt_PreserveKernel
import Theorems.Thm_DyckAlgebra_DyckRepU_theta_dps_pow_eq

set_option autoImplicit true
open DyckAlgebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)
namespace DyckAlgebra.DyckRepU
theorem _root_.solution (k : ℕ) (e0 : ρ.carrier)
    (hsStar : ∀ j, 1 ≤ j → ρ.sStarElt * ρ.dps ^ j * e0 = 0)
    (hI1 : (ρ.dm * ρ.dps - 1) * ρ.dps ^ k * e0 = 0) :
    (ρ.dm * ρ.Θdps - 1) * ρ.Θdps ^ k * e0 = 0 := by
  have hk : ρ.Θdps ^ k * e0 = ρ.dps ^ k * e0 := ρ.theta_dps_pow_eq k e0 hsStar
  have hk1 : ρ.Θdps ^ (k + 1) * e0 = ρ.dps ^ (k + 1) * e0 :=
    ρ.theta_dps_pow_eq (k + 1) e0 hsStar
  have expand : (ρ.dm * ρ.Θdps - 1) * ρ.Θdps ^ k * e0
      = ρ.dm * (ρ.Θdps ^ (k + 1) * e0) - ρ.Θdps ^ k * e0 := by
    rw [pow_succ']; noncomm_ring
  have collapse : ρ.dm * (ρ.dps ^ (k + 1) * e0) - ρ.dps ^ k * e0
      = (ρ.dm * ρ.dps - 1) * ρ.dps ^ k * e0 := by
    rw [pow_succ']; noncomm_ring
  rw [expand, hk, hk1, collapse, hI1]
end DyckAlgebra.DyckRepU
