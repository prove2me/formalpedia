-- Prove2me | solution 1 for Formalism.L2.G.Cmp.extK_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:26:17.295184+00:00
-- url     : https://prove2.me/submissions/f9a8943b-0c96-4fee-8896-a6fc5bc0a3cb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_ComparisonMaps_IsComplRatCompl
import Theorems.Thm_Formalism_L2_G_Cmp_extK_apply

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
    (hli : LinearIndependent Kf fun i => c0 (b i)) (KL : V0 →ₗ[LL] V1) (g : W0 →ₗ[Kf] W1)
    (hg : ∀ x, g (c0 x) = c1 (KL x)) (y : W0) (hy : y ∈ spanK c0) : g y = extK c0 c1 b hli KL y := by
  unfold spanK at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, rfl⟩ := hz
    rw [hg, extK_apply]
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, map_add, hy, hz]
  | smul a y _ hy => rw [map_smul, map_smul, hy]
end Formalism.L2.G.Cmp
