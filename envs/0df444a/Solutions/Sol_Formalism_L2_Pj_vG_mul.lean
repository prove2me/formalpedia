-- Prove2me | solution 1 for Formalism.L2.Pj.vG_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:22:09.036814+00:00
-- url     : https://prove2.me/submissions/2468414d-3f20-411e-b68e-3830b053377b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ErealAddIInf
import Theorems.Thm_Formalism_L2_Pj_incG_apply
import Theorems.Thm_Formalism_L2_Pj_vG_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
variable {K R M W : Type} [Field K] [CommRing R] [Algebra K R] [AddCommMonoid M] (key : W → M)
  (C : W → Submodule K R)
variable {v : R → EReal}
namespace Formalism.L2.Pj
theorem _root_.solution (h0 : v 0 = ⊤) (hm : ∀ r s, v (r * s) = v r + v s) (w w' : W) (F : C w) (F' : C w') :
    vG v (incG key C w F * incG key C w' F') = vG v (incG key C w F) + vG v (incG key C w' F') := by
  rw [incG_apply, incG_apply, AddMonoidAlgebra.single_mul_single, vG_single h0, vG_single h0, vG_single h0, hm]
end Formalism.L2.Pj
