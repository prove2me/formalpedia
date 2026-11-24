-- Prove2me | solution 1 for DyckAlgebra.DyckRepU.yy_comm_Tinv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:19:01.735569+00:00
-- url     : https://prove2.me/submissions/6c219688-dcf0-4350-967e-232abe330568

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
import Theorems.Thm_DyckAlgebra_AqtAction_apply_add
import Theorems.Thm_DyckAlgebra_AqtAction_apply_mul
import Theorems.Thm_DyckAlgebra_AqtAction_apply_one
attribute [local simp] DyckAlgebra.AqtAction.apply_add
attribute [local simp] DyckAlgebra.AqtAction.apply_mul
attribute [local simp] DyckAlgebra.AqtAction.apply_one



set_option autoImplicit true
open DyckAlgebra
open scoped BigOperators
universe v
attribute [instance] ThetaData.ring ThetaData.algebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)
namespace DyckAlgebra.DyckRepU
theorem _root_.solution (i j : ℕ) (h : i ≠ j ∧ i ≠ j + 1) :
    ρ.yy i * ρ.Tinv j = ρ.Tinv j * ρ.yy i := by
  have hcomm := ρ.yTcomm i j h
  calc
    ρ.yy i * ρ.Tinv j = 1 * ρ.yy i * ρ.Tinv j := by rw [one_mul]
    _ = (ρ.Tinv j * ρ.T j) * ρ.yy i * ρ.Tinv j := by rw [ρ.TinvR]
    _ = ρ.Tinv j * (ρ.T j * ρ.yy i) * ρ.Tinv j := by simp only [mul_assoc]
    _ = ρ.Tinv j * (ρ.yy i * ρ.T j) * ρ.Tinv j := by rw [hcomm]
    _ = ρ.Tinv j * ρ.yy i * (ρ.T j * ρ.Tinv j) := by simp only [mul_assoc]
    _ = ρ.Tinv j * ρ.yy i := by rw [ρ.TinvL, mul_one]
end DyckAlgebra.DyckRepU
