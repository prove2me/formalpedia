-- Prove2me | solution 1 for DyckAlgebra.DyckRepU.intertwine_dOne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:50:44.040362+00:00
-- url     : https://prove2.me/submissions/c30d6229-fa3a-4b91-af84-005d98173a4d

import Definitions.Def_RequestProject_Aqt_PreserveKernel
import Definitions.Def_RequestProject_Aqt_DGamma
import Theorems.Thm_DyckAlgebra_DyckRepU_thetaDOneWord_eq_series
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
    (hps : U * ρ.dps = ρ.Θdps * U) :
    U * ρ.dOneWord = ρ.dPositiveSeries * U := by
  unfold dOneWord
  calc
    U * (ρ.dm * -ρ.yy 1 * ρ.dps) = (U * ρ.dm) * -ρ.yy 1 * ρ.dps := by
      simp only [mul_assoc]
    _ = (ρ.dm * U) * -ρ.yy 1 * ρ.dps := by rw [hm]
    _ = ρ.dm * (U * -ρ.yy 1) * ρ.dps := by simp only [mul_assoc]
    _ = ρ.dm * (-ρ.Θy1 * U) * ρ.dps := by rw [mul_neg, hy, neg_mul]
    _ = ρ.dm * -ρ.Θy1 * (U * ρ.dps) := by simp only [mul_assoc]
    _ = ρ.dm * -ρ.Θy1 * (ρ.Θdps * U) := by rw [hps]
    _ = ρ.thetaDOneWord * U := by simp only [thetaDOneWord, mul_assoc]
    _ = ρ.dPositiveSeries * U := by rw [ρ.thetaDOneWord_eq_series]
end DyckAlgebra.DyckRepU
