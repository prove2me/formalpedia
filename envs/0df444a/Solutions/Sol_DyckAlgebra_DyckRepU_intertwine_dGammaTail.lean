-- Prove2me | solution 1 for DyckAlgebra.DyckRepU.intertwine_dGammaTail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:23:21.699654+00:00
-- url     : https://prove2.me/submissions/01c15726-544c-49b3-bc14-ef168a148e5d

import Definitions.Def_RequestProject_Aqt_PreserveKernel
import Definitions.Def_RequestProject_Aqt_DGamma
import Theorems.Thm_DyckAlgebra_DyckRepU_intertwine_pow
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
    (hy : U * ρ.yy 1 = ρ.Θy1 * U)
    (hz : U * ρ.zz 1 = ρ.Θz1 * U)
    (hp : U * ρ.dp = ρ.Θdp * U) :
    ∀ gs : List ℕ, U * ρ.dGammaTail gs = ρ.thetaDGammaTail gs * U := by
  intro gs
  induction gs with
  | nil =>
    simp [dGammaTail, thetaDGammaTail]
    calc U * (ρ.zz 1 * ρ.dp) = (U * ρ.zz 1) * ρ.dp := by rw [mul_assoc]
      _ = (ρ.Θz1 * U) * ρ.dp := by rw [hz]
      _ = ρ.Θz1 * (U * ρ.dp) := by rw [mul_assoc]
      _ = ρ.Θz1 * (ρ.Θdp * U) := by rw [hp]
      _ = ρ.Θz1 * ρ.Θdp * U := by rw [mul_assoc]
  | cons g gs ih =>
    simp [dGammaTail, thetaDGammaTail]
    -- First establish that U intertwines -ρ.yy 1 with -ρ.Θy1
    have hy_neg : U * (-ρ.yy 1) = (-ρ.Θy1) * U := by
      calc U * (-ρ.yy 1) = -(U * ρ.yy 1) := by rw [mul_neg]
        _ = -(ρ.Θy1 * U) := by rw [hy]
        _ = (-ρ.Θy1) * U := by rw [neg_mul]
    -- Get the power version
    have hy_pow : U * (-ρ.yy 1) ^ g = (-ρ.Θy1) ^ g * U := intertwine_pow ρ hy_neg g
    -- Now rewrite step by step
    rw [mul_assoc (ρ.zz 1) ((-ρ.yy 1) ^ g) (ρ.dGammaTail gs)]
    rw [← mul_assoc U (ρ.zz 1) ((-ρ.yy 1) ^ g * ρ.dGammaTail gs)]
    rw [hz]
    rw [mul_assoc ρ.Θz1 U]
    rw [← mul_assoc U]
    rw [hy_pow]
    rw [mul_assoc ((-ρ.Θy1) ^ g) U]
    rw [ih]
    rw [← mul_assoc ((-ρ.Θy1) ^ g) (ρ.thetaDGammaTail gs) U]
    simp only [mul_assoc]
end DyckAlgebra.DyckRepU
