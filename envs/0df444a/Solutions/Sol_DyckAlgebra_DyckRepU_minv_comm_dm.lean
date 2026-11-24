-- Prove2me | solution 1 for DyckAlgebra.DyckRepU.minv_comm_dm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:20:21.082817+00:00
-- url     : https://prove2.me/submissions/c415086c-1614-4026-9f7a-b17dffaba38c

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
import Theorems.Thm_DyckAlgebra_DyckRepU_sStarElt_comm_dm
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
theorem _root_.solution : ρ.minv * ρ.dm = ρ.dm * ρ.minv := by
  have hs : (1 + ρ.sStarElt) * ρ.dm = ρ.dm * (1 + ρ.sStarElt) := by
    simp [add_mul, mul_add, ρ.sStarElt_comm_dm]
  have hmL : (1 + ρ.sStarElt) * ρ.minv = 1 := by
    simpa [sStarElt] using ρ.mL
  have hmR : ρ.minv * (1 + ρ.sStarElt) = 1 := by
    simpa [sStarElt] using ρ.mR
  calc
    ρ.minv * ρ.dm = ρ.minv * ρ.dm * ((1 + ρ.sStarElt) * ρ.minv) := by
      rw [hmL, mul_one]
    _ = ρ.minv * (ρ.dm * (1 + ρ.sStarElt)) * ρ.minv := by simp only [mul_assoc]
    _ = ρ.minv * ((1 + ρ.sStarElt) * ρ.dm) * ρ.minv := by rw [hs]
    _ = (ρ.minv * (1 + ρ.sStarElt)) * ρ.dm * ρ.minv := by simp only [mul_assoc]
    _ = ρ.dm * ρ.minv := by rw [hmR, one_mul]
end DyckAlgebra.DyckRepU
