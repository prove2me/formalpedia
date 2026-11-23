-- Prove2me | solution 1 for Formalism.L2.Pj.vG_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:19:10.821128+00:00
-- url     : https://prove2.me/submissions/06bab4da-1954-495a-83c7-6074814bb4c8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ErealAddIInf

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
theorem _root_.solution (ha : ∀ r s, min (v r) (v s) ≤ v (r + s)) (x y : AddMonoidAlgebra R M) :
    min (vG v x) (vG v y) ≤ vG v (x + y) := by
  refine le_iInf fun m => ?_
  have : (x + y).coeff m = x.coeff m + y.coeff m := by simp
  rw [this]
  exact (min_le_min (iInf_le _ m) (iInf_le _ m)).trans (ha _ _)
end Formalism.L2.Pj
