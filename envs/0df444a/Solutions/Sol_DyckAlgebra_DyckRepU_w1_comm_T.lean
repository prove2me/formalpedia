-- Prove2me | solution 1 for DyckAlgebra.DyckRepU.w1_comm_T
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:18:29.629484+00:00
-- url     : https://prove2.me/submissions/c3354299-184a-4d23-bba5-34d4832164d0

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
theorem _root_.solution (j : ℕ) (hj : 2 ≤ j) : ρ.w 1 * ρ.T j = ρ.T j * ρ.w 1 := by
  have h_comm : (1 + ρ.u • ρ.yy 1) * ρ.w 1 = 1 ∧ ρ.w 1 * (1 + ρ.u • ρ.yy 1) = 1 := by
    exact ⟨ ρ.wL 1, ρ.wR 1 ⟩;
  have h_comm : (1 + ρ.u • ρ.yy 1) * ρ.T j = ρ.T j * (1 + ρ.u • ρ.yy 1) := by
    simp +decide [ add_mul, mul_add, ρ.yTcomm 1 j ( by omega ) ];
  apply_fun (fun x => ρ.w 1 * x) at h_comm;
  grind
end DyckAlgebra.DyckRepU
