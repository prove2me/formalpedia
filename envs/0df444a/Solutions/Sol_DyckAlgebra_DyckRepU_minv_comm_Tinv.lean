-- Prove2me | solution 1 for DyckAlgebra.DyckRepU.minv_comm_Tinv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:23:14.654882+00:00
-- url     : https://prove2.me/submissions/64b84daf-e9ac-430b-a96f-dcd8695cd577

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
import Theorems.Thm_DyckAlgebra_DyckRepU_sStarElt_comm_Tinv
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
theorem _root_.solution (j : ℕ) (hj : 2 ≤ j) :
    ρ.minv * ρ.Tinv j = ρ.Tinv j * ρ.minv := by
  have := ρ.mL;
  have := ρ.mR;
  convert congr_arg ( fun x => ρ.minv * x * ρ.Tinv j ) this using 1;
  · simp +decide [ this ];
  · have h_comm : (1 + (ρ.u • ρ.yy 1 - ρ.u • (ρ.zz 1 * ρ.yy 1))) * ρ.Tinv j = ρ.Tinv j * (1 + (ρ.u • ρ.yy 1 - ρ.u • (ρ.zz 1 * ρ.yy 1))) := by
      have := ρ.sStarElt_comm_Tinv j hj;
      simp_all +decide [ add_mul, mul_add, DyckRepU.sStarElt ];
    convert congr_arg ( fun x => ρ.minv * x * ρ.minv ) h_comm using 1 <;> simp +decide [mul_assoc];
    · simp +decide [ ← mul_assoc, this ];
    · simp +decide [‹(1 + (ρ.u • ρ.yy 1 - ρ.u • (ρ.zz 1 * ρ.yy 1))) * ρ.minv = 1›]
end DyckAlgebra.DyckRepU
