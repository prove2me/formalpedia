-- Prove2me | solution 1 for DyckAlgebra.AqtAction.apply_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:51:23.739031+00:00
-- url     : https://prove2.me/submissions/e5cc5bcf-d93c-46ec-a66c-df068e798eb9

import Definitions.Def_RequestProject_Aqt_Algebra
import Definitions.Def_RequestProject_Aqt_Rep

set_option autoImplicit true
open DyckAlgebra
universe v
attribute [instance] AqtAction.addCommGroup AqtAction.module
open DyckAlgebra.AqtAction
variable {𝕜 : Type*} [Field 𝕜] {q t : 𝕜} (ρ : AqtAction 𝕜 q t)
namespace DyckAlgebra.AqtAction
theorem _root_.solution (a b : Aqt q t) (v : ρ.carrier) :
    ρ.apply (a + b) v = ρ.apply a v + ρ.apply b v := by
  simp [apply]
end DyckAlgebra.AqtAction
