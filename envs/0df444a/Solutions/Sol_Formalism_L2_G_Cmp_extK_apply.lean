-- Prove2me | solution 1 for Formalism.L2.G.Cmp.extK_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:17:56.405103+00:00
-- url     : https://prove2.me/submissions/4fd25a85-cd61-47c8-a8e1-e833d1f2ee20

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_ComparisonMaps_IsComplRatCompl
import Theorems.Thm_Formalism_L2_G_Cmp_extK_basis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Cmp
variable {LL Kf : Type*} [Field LL] [Field Kf] {e : LL →+* Kf}
  {V0 V1 W0 W1 ι : Type*} [AddCommGroup V0] [Module LL V0] [AddCommGroup V1] [Module LL V1]
  [AddCommGroup W0] [Module Kf W0] [AddCommGroup W1] [Module Kf W1]
namespace Formalism.L2.G.Cmp
theorem _root_.solution (c0 : V0 →ₛₗ[e] W0) (c1 : V1 →ₛₗ[e] W1) (b : Module.Basis ι LL V0)
    (hli : LinearIndependent Kf fun i => c0 (b i)) (KL : V0 →ₗ[LL] V1) (x : V0) :
    extK c0 c1 b hli KL (c0 x) = c1 (KL x) := by
  have e1 : ⇑(extK c0 c1 b hli KL) ∘ (fun i => c0 (b i)) = fun i => c1 (KL (b i)) :=
    funext fun i => extK_basis c0 c1 b hli KL i
  rw [← lc_repr_lemma c0 b x, Finsupp.apply_linearCombination, e1]
  exact lc_repr_lemma (c1.comp KL) b x
end Formalism.L2.G.Cmp
