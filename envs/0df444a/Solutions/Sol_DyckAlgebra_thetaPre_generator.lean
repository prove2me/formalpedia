-- Prove2me | solution 1 for DyckAlgebra.thetaPre_generator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:23:41.395459+00:00
-- url     : https://prove2.me/submissions/3a6f8f65-2063-4adb-a98a-addc056e8862

import Definitions.Def_RequestProject_Aqt_Theta
import Definitions.Def_RequestProject_Aqt_ThetaDescent
import Theorems.Thm_DyckAlgebra_AqtAction_apply_add
import Theorems.Thm_DyckAlgebra_AqtAction_apply_mul
import Theorems.Thm_DyckAlgebra_AqtAction_apply_one
attribute [local simp] DyckAlgebra.AqtAction.apply_add
attribute [local simp] DyckAlgebra.AqtAction.apply_mul
attribute [local simp] DyckAlgebra.AqtAction.apply_one



set_option autoImplicit true
open DyckAlgebra
universe v
variable {𝕜 : Type*} [Field 𝕜] {q t : 𝕜}
variable {C : Type v} [Ring C] [Algebra 𝕜 C]
namespace DyckAlgebra
theorem _root_.solution (thetaGen : Gen → C) (g : Gen) :
    thetaPre thetaGen (FreeAlgebra.ι 𝕜 g) = thetaGen g := by
  simp [thetaPre]
end DyckAlgebra
