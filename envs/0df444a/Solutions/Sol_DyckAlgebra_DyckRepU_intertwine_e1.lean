-- Prove2me | solution 1 for DyckAlgebra.DyckRepU.intertwine_e1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:50:45.596541+00:00
-- url     : https://prove2.me/submissions/d930037e-f1bd-4a7f-9177-e21cdb4307d6

import Definitions.Def_RequestProject_Aqt_PreserveKernel
import Definitions.Def_RequestProject_Aqt_DGamma
import Theorems.Thm_DyckAlgebra_DyckRepU_thetaE1Word_eq
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
theorem _root_.solution (U : ρ.carrier) (hlevel : ρ.level = 0)
    (hm : U * ρ.dm = ρ.dm * U)
    (hp : U * ρ.dp = ρ.Θdp * U) :
    U * ρ.e1Word =
      (ρ.e1Word + (ρ.dPositiveSeries - ρ.dOneWord)) * U := by
  unfold e1Word
  calc
    U * (ρ.dm * ρ.dp) = (U * ρ.dm) * ρ.dp := by rw [mul_assoc]
    _ = (ρ.dm * U) * ρ.dp := by rw [hm]
    _ = ρ.dm * (U * ρ.dp) := by rw [mul_assoc]
    _ = ρ.dm * (ρ.Θdp * U) := by rw [hp]
    _ = ρ.thetaE1Word * U := by simp only [thetaE1Word, mul_assoc]
    _ = (ρ.e1Word + (ρ.dPositiveSeries - ρ.dOneWord)) * U := by
      rw [ρ.thetaE1Word_eq hlevel]
end DyckAlgebra.DyckRepU
