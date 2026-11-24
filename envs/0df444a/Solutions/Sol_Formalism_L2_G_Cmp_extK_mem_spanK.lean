-- Prove2me | solution 1 for Formalism.L2.G.Cmp.extK_mem_spanK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:58:11.396282+00:00
-- url     : https://prove2.me/submissions/a1df4572-a7be-4415-b2b7-65a81b8ce38d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_ComparisonMaps_IsComplRatCompl

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
    (hli : LinearIndependent Kf fun i => c0 (b i)) (KL : V0 →ₗ[LL] V1) (y : W0) :
    extK c0 c1 b hli KL y ∈ spanK c1 := by
  have h1 : extK c0 c1 b hli KL y ∈ LinearMap.range (Finsupp.linearCombination Kf fun i => c1 (KL (b i))) :=
    LinearMap.mem_range.2 ⟨_, rfl⟩
  rw [Finsupp.range_linearCombination] at h1
  exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨KL (b i), rfl⟩) h1
end Formalism.L2.G.Cmp
