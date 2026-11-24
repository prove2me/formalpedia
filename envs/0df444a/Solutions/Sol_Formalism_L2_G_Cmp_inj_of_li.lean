-- Prove2me | solution 1 for Formalism.L2.G.Cmp.inj_of_li
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:37.661908+00:00
-- url     : https://prove2.me/submissions/f08f4b12-eab1-499f-8d8b-e4ccfd1b65ae

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
theorem _root_.solution (c0 : V0 →ₛₗ[e] W0) (b : Module.Basis ι LL V0)
    (hli : LinearIndependent Kf fun i => c0 (b i)) : Function.Injective c0 := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h1 := linearIndependent_iff.1 hli _ ((lc_repr_lemma c0 b x).trans hx)
  have h2 : b.repr x = 0 := by
    ext i
    have h3 := DFunLike.congr_fun h1 i
    simpa using h3
  exact b.repr.map_eq_zero_iff.1 h2
end Formalism.L2.G.Cmp
