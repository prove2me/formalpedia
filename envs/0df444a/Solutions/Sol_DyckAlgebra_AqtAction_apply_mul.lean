-- Prove2me | solution 1 for DyckAlgebra.AqtAction.apply_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:52:57.077873+00:00
-- url     : https://prove2.me/submissions/703ab3e4-d65a-4f43-bcc4-026ed0bb23ef

import Definitions.Def_RequestProject_Aqt_Algebra
import Definitions.Def_RequestProject_Aqt_Rep
import Theorems.Thm_DyckAlgebra_AqtAction_apply_add
attribute [local simp] DyckAlgebra.AqtAction.apply_add

set_option autoImplicit true
open DyckAlgebra
universe v
attribute [instance] AqtAction.addCommGroup AqtAction.module
open DyckAlgebra.AqtAction
variable {𝕜 : Type*} [Field 𝕜] {q t : 𝕜} (ρ : AqtAction 𝕜 q t)
namespace DyckAlgebra.AqtAction
theorem _root_.solution (a b : Aqt q t) (v : ρ.carrier) :
    ρ.apply (a * b) v = ρ.apply a (ρ.apply b v) := by
  simp [apply]
end DyckAlgebra.AqtAction
