-- Prove2me | solution 1 for DyckAlgebra.DyckRepU.theta_R2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:49:45.939473+00:00
-- url     : https://prove2.me/submissions/d0e78dea-4c17-4bed-9326-d47b74fcb6bd

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
import Theorems.Thm_DyckAlgebra_DyckRepU_sElt_comm_T
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
theorem _root_.solution (i : ℕ) (h : 1 ≤ i) : ρ.Θdp * ρ.T i = ρ.T (i+1) * ρ.Θdp := by
  unfold DyckRepU.Θdp;
  have := ρ.R2 i h;
  simp_all +decide [ mul_assoc, sub_mul, mul_sub ];
  simp +decide only [← mul_assoc, sElt_comm_T ρ (i + 1) (by linarith)]
end DyckAlgebra.DyckRepU
