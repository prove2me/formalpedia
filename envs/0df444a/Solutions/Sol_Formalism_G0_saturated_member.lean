-- Prove2me | solution 1 for Formalism.G0.saturated_member
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:24.862102+00:00
-- url     : https://prove2.me/submissions/122249b6-1188-446e-86af-2f2c6a339e33

import Definitions.Def_Formalism_SubspaceCounting_Statement
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_SaturatedMember

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.G0
namespace Formalism.G0
theorem _root_.solution : SaturatedMember := by
  intro O M _ _ _ _ π hπ M' P τ hsat
  have hπτ : π ^ τ ≠ 0 := pow_ne_zero _ hπ
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨⟨_, hxT⟩, hxM'⟩ := hx
    rw [Submodule.ideal_span_singleton_smul] at hxT ⊢
    obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hxT
    have hy : y ∈ M' := hsat _ _ hπτ hxM'
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨y, hy, rfl⟩
  · set N := P ⊓ (Ideal.span {π ^ τ}) • (⊤ : Submodule O M)
    let f : (M' ⧸ Submodule.comap M'.subtype N) →ₗ[O] (M ⧸ N) :=
      Submodule.mapQ _ _ M'.subtype le_rfl
    have hf : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ]
      simp
    exact Module.length_le_of_injective f hf
end Formalism.G0
