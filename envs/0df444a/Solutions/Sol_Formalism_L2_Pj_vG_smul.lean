-- Prove2me | solution 1 for Formalism.L2.Pj.vG_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:24:03.320149+00:00
-- url     : https://prove2.me/submissions/32b92cb3-a78f-4da5-990b-da34748c8a06

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ErealAddIInf
import Theorems.Thm_Formalism_L2_Pj_ereal_add_iInf

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
theorem _root_.solution {a : K} {t : ℝ} (hs : ∀ r, v (a • r) = (t : EReal) + v r) (x : AddMonoidAlgebra R M) :
    vG v (a • x) = (t : EReal) + vG v x := by
  unfold vG
  rw [ereal_add_iInf]
  refine iInf_congr fun m => ?_
  have : (a • x).coeff m = a • x.coeff m := by simp
  rw [this, hs]
end Formalism.L2.Pj
