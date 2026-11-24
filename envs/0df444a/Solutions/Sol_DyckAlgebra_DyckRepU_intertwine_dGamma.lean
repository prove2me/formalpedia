-- Prove2me | solution 1 for DyckAlgebra.DyckRepU.intertwine_dGamma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:26:50.594446+00:00
-- url     : https://prove2.me/submissions/d2ad82c5-37a5-4831-a35d-477861f2dc4f

import Definitions.Def_RequestProject_Aqt_PreserveKernel
import Definitions.Def_RequestProject_Aqt_DGamma
import Theorems.Thm_DyckAlgebra_DyckRepU_intertwine_dGamma_cons
import Theorems.Thm_DyckAlgebra_AqtAction_apply_add
import Theorems.Thm_DyckAlgebra_AqtAction_apply_mul
import Theorems.Thm_DyckAlgebra_AqtAction_apply_one
attribute [local simp] DyckAlgebra.AqtAction.apply_add
attribute [local simp] DyckAlgebra.AqtAction.apply_mul
attribute [local simp] DyckAlgebra.AqtAction.apply_one



set_option autoImplicit true
open DyckAlgebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)
namespace DyckAlgebra.DyckRepU
theorem _root_.solution (U : ρ.carrier)
    (hm : U * ρ.dm = ρ.dm * U)
    (hy : U * ρ.yy 1 = ρ.Θy1 * U)
    (hz : U * ρ.zz 1 = ρ.Θz1 * U)
    (hp : U * ρ.dp = ρ.Θdp * U) :
    ∀ γ : List ℕ, U * ρ.dGamma γ = ρ.thetaDGamma γ * U := by
  intro γ
  cases γ with
  | nil => simp [dGamma, thetaDGamma]
  | cons g gs => exact ρ.intertwine_dGamma_cons U g gs hm hy hz hp
end DyckAlgebra.DyckRepU
