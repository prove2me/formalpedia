-- Prove2me | solution 1 for DyckAlgebra.DyckRepU.intertwine_dGamma_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:25:19.472805+00:00
-- url     : https://prove2.me/submissions/b5bee695-f3db-428e-b80b-e4c335ba3acd

import Definitions.Def_RequestProject_Aqt_PreserveKernel
import Definitions.Def_RequestProject_Aqt_DGamma
import Theorems.Thm_DyckAlgebra_DyckRepU_intertwine_pow
import Theorems.Thm_DyckAlgebra_DyckRepU_intertwine_dGammaTail
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
theorem _root_.solution (U : ρ.carrier) (g : ℕ) (gs : List ℕ)
    (hm : U * ρ.dm = ρ.dm * U)
    (hy : U * ρ.yy 1 = ρ.Θy1 * U)
    (hz : U * ρ.zz 1 = ρ.Θz1 * U)
    (hp : U * ρ.dp = ρ.Θdp * U) :
    U * ρ.dGamma (g :: gs) = ρ.thetaDGamma (g :: gs) * U := by
  have hneg : U * (-ρ.yy 1) = (-ρ.Θy1) * U := by
    calc
      U * (-ρ.yy 1) = -(U * ρ.yy 1) := by rw [mul_neg]
      _ = -(ρ.Θy1 * U) := by rw [hy]
      _ = (-ρ.Θy1) * U := by rw [neg_mul]
  have hpow := ρ.intertwine_pow hneg (g - 1)
  have htail := ρ.intertwine_dGammaTail U hy hz hp gs
  simp only [dGamma, thetaDGamma]
  calc
    U * (ρ.dm * (-ρ.yy 1) ^ (g - 1) * ρ.dGammaTail gs) =
        (U * ρ.dm) * (-ρ.yy 1) ^ (g - 1) * ρ.dGammaTail gs := by
          simp only [mul_assoc]
    _ = (ρ.dm * U) * (-ρ.yy 1) ^ (g - 1) * ρ.dGammaTail gs := by rw [hm]
    _ = ρ.dm * (U * (-ρ.yy 1) ^ (g - 1)) * ρ.dGammaTail gs := by
          simp only [mul_assoc]
    _ = ρ.dm * ((-ρ.Θy1) ^ (g - 1) * U) * ρ.dGammaTail gs := by rw [hpow]
    _ = ρ.dm * (-ρ.Θy1) ^ (g - 1) * (U * ρ.dGammaTail gs) := by
          simp only [mul_assoc]
    _ = ρ.dm * (-ρ.Θy1) ^ (g - 1) * (ρ.thetaDGammaTail gs * U) := by rw [htail]
    _ = ρ.dm * (-ρ.Θy1) ^ (g - 1) * ρ.thetaDGammaTail gs * U := by
          simp only [mul_assoc]
end DyckAlgebra.DyckRepU
