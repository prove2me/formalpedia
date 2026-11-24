-- Prove2me | solution 1 for DyckAlgebra.thetaDescent_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:51:00.620464+00:00
-- url     : https://prove2.me/submissions/9ef01646-2699-47a0-b85b-352787512a2f

import Definitions.Def_RequestProject_Aqt_Theta
import Definitions.Def_RequestProject_Aqt_ThetaDescent
import Theorems.Thm_DyckAlgebra_thetaPre_generator
import Theorems.Thm_DyckAlgebra_AqtAction_apply_add
import Theorems.Thm_DyckAlgebra_AqtAction_apply_mul
import Theorems.Thm_DyckAlgebra_AqtAction_apply_one
attribute [local simp] DyckAlgebra.AqtAction.apply_add
attribute [local simp] DyckAlgebra.AqtAction.apply_mul
attribute [local simp] DyckAlgebra.AqtAction.apply_one


attribute [local simp] DyckAlgebra.thetaPre_generator

set_option autoImplicit true
open DyckAlgebra
universe v
variable {𝕜 : Type*} [Field 𝕜] {q t : 𝕜}
variable {C : Type v} [Ring C] [Algebra 𝕜 C]
namespace DyckAlgebra
theorem _root_.solution (thetaGen : Gen → C)
    (preserves : ∀ ⦃a b : Pre 𝕜⦄, Rel q t a b →
      thetaPre thetaGen a = thetaPre thetaGen b)
    (a : Pre 𝕜) :
    thetaDescent thetaGen preserves (RingQuot.mkAlgHom 𝕜 (Rel q t) a) =
      thetaPre thetaGen a := by
  simp [thetaDescent]
end DyckAlgebra
