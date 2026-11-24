-- Prove2me | solution 1 for DyckAlgebra.DyckRepU.theta_dps_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:24:03.530372+00:00
-- url     : https://prove2.me/submissions/a44d1707-837a-4847-ac3a-4efdbdd3e356

import Definitions.Def_RequestProject_Aqt_Theta
import Definitions.Def_RequestProject_Aqt_PreserveKernel
import Theorems.Thm_DyckAlgebra_DyckRepU_minv_mul_dps_pow
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
theorem _root_.solution (k : ℕ) (e0 : ρ.carrier)
    (hsStar : ∀ j, 1 ≤ j → ρ.sStarElt * ρ.dps ^ j * e0 = 0) :
    ρ.Θdps ^ k * e0 = ρ.dps ^ k * e0 := by
  induction' k with k ih;
  · simp +decide;
  · convert minv_mul_dps_pow ρ ( k + 1 ) e0 ( hsStar ( k + 1 ) ( Nat.succ_pos k ) ) using 1;
    convert congr_arg ( fun x => ρ.minv * ρ.dps * x ) ih using 1 <;> simp +decide [ pow_succ', mul_assoc ];
    simp +decide [ ← mul_assoc, DyckRepU.Θdps ]
end DyckAlgebra.DyckRepU
