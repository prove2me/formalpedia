-- Prove2me | solution 1 for Formalism.L2.NCov.repr_transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:13:59.957378+00:00
-- url     : https://prove2.me/submissions/570b4409-7675-4e0e-8dd1-c319175b2a32

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverPoly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.NCov
open Module
variable {K₁ K₂ V₁ V₂ : Type*} [Field K₁] [Field K₂] [AddCommGroup V₁] [Module K₁ V₁] [AddCommGroup V₂]
  [Module K₂ V₂]
namespace Formalism.L2.NCov
theorem _root_.solution (σ : K₁ →+* K₂) (ι : V₁ →ₛₗ[σ] V₂) {n : Type*} [Fintype n] [DecidableEq n]
    (b : Module.Basis n K₁ V₁) (hli : LinearIndependent K₂ (ι ∘ b))
    (hsp : Submodule.span K₂ (Set.range (ι ∘ b)) = ⊤) (x : V₁) (r : n) :
    (Module.Basis.mk hli hsp.ge).repr (ι x) r = σ (b.repr x r) := by
  have hx : ι x = ∑ i, σ (b.repr x i) • (Module.Basis.mk hli hsp.ge) i := by
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Module.Basis.mk_apply, Function.comp_apply]
    first
      | exact LinearMap.map_smulₛₗ ι (b.repr x i) (b i)
      | exact map_smulₛₗ ι (b.repr x i) (b i)
      | simp
  rw [hx, Module.Basis.repr_sum_self]
end Formalism.L2.NCov
