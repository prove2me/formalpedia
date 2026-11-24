-- Prove2me | solution 1 for DyckAlgebra.DyckRepU.minv_mul_dps_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:21:36.24145+00:00
-- url     : https://prove2.me/submissions/efd1ce61-797c-430c-a0b3-3e53550ca379

import Definitions.Def_RequestProject_Aqt_Theta
import Definitions.Def_RequestProject_Aqt_PreserveKernel
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
theorem _root_.solution (j : ℕ) (e0 : ρ.carrier)
    (hsStar : ρ.sStarElt * ρ.dps ^ j * e0 = 0) :
    ρ.minv * ρ.dps ^ j * e0 = ρ.dps ^ j * e0 := by
  have h_sStarElt : (1 + ρ.sStarElt) * (ρ.dps ^ j * e0) = ρ.dps ^ j * e0 := by
    simp_all +decide [ add_mul, mul_assoc ];
  have h_minv : ρ.minv * (1 + ρ.sStarElt) = 1 := by
    exact ρ.mR;
  have h_minv : ρ.minv * (ρ.dps ^ j * e0) = ρ.minv * ((1 + ρ.sStarElt) * (ρ.dps ^ j * e0)) := by
    rw [h_sStarElt];
  rw [ mul_assoc, h_minv, ← mul_assoc, ‹ρ.minv * ( 1 + ρ.sStarElt ) = 1›, one_mul ]
end DyckAlgebra.DyckRepU
