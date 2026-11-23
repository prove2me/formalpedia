-- Prove2me | solution 1 for Formalism.L2.Pj.vG_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:19:10.523025+00:00
-- url     : https://prove2.me/submissions/408c8c11-6908-448b-b074-c8c35f7cfa4f

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
theorem _root_.solution (h0 : v 0 = ⊤) (hb : ∀ r, v r ≠ ⊥) (x : AddMonoidAlgebra R M) : vG v x ≠ ⊥ := by
  classical
  have hT : x.coeff.support.inf (fun m => v (x.coeff m)) ≤ vG v x := by
    refine le_iInf fun m => ?_
    by_cases hm : m ∈ x.coeff.support
    · exact Finset.inf_le hm
    · rw [Finsupp.notMem_support_iff.mp hm, h0]; exact le_top
  have hne : x.coeff.support.inf (fun m => v (x.coeff m)) ≠ ⊥ := by
    rw [Ne, Finset.inf_eq_bot_iff]; push Not
    exact fun m _ => hb _
  intro h
  exact hne (le_bot_iff.mp (h ▸ hT))
end Formalism.L2.Pj
