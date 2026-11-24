-- Prove2me | solution 1 for Formalism.G0.LengthLayersP.length_sup_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:38.008532+00:00
-- url     : https://prove2.me/submissions/0ede032e-853d-4a2e-9a70-59c025e31c0e

import Definitions.Def_Formalism_SubspaceCounting_Statement
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_LengthLayers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0
open Formalism.G0.LengthLayersP
variable {O : Type} [CommRing O]
namespace Formalism.G0.LengthLayersP
theorem _root_.solution {X : Type} [AddCommGroup X] [Module O X] (A B : Submodule O X) :
    Module.length O ↥(A ⊔ B) ≤ Module.length O ↥A + Module.length O ↥B := by
  let f : ↥A × ↥B →ₗ[O] ↥(A ⊔ B) :=
    LinearMap.coprod (Submodule.inclusion le_sup_left) (Submodule.inclusion le_sup_right)
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  have hprod : Module.length O (↥A × ↥B) = Module.length O ↥A + Module.length O ↥B :=
    Module.length_eq_add_of_exact (LinearMap.inl O ↥A ↥B) (LinearMap.snd O ↥A ↥B)
      LinearMap.inl_injective LinearMap.snd_surjective (by
        rintro ⟨a, b⟩
        constructor
        · intro h
          exact ⟨a, by simp [show b = 0 from h]⟩
        · rintro ⟨a', h⟩
          exact (congrArg Prod.snd h).symm)
  exact hprod ▸ Module.length_le_of_surjective f hf
end Formalism.G0.LengthLayersP
