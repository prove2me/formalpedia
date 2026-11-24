-- Prove2me | solution 1 for DyckAlgebra.DyckRepU.sStar_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:20:09.137352+00:00
-- url     : https://prove2.me/submissions/880089e0-4458-47f7-8aa9-200b672c2d32

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
import Theorems.Thm_DyckAlgebra_Theta_one_add_sStar_eq
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
theorem _root_.solution : 1 + ρ.sStarElt = (1 + ρ.u • ρ.yy 1) * (1 - ρ.s2Elt) := by
  have h := DyckAlgebra.Theta.one_add_sStar_eq ρ.u (ρ.w 1) (ρ.yy 1) (ρ.zz 1) (ρ.wL 1)
  have hs : ρ.sStarElt = Theta.sStar ρ.u (ρ.yy 1) (ρ.zz 1) := by
    unfold DyckRepU.sStarElt Theta.sStar
    simp +decide [sub_mul, smul_sub]
  simpa [hs, DyckRepU.s2Elt] using h
end DyckAlgebra.DyckRepU
