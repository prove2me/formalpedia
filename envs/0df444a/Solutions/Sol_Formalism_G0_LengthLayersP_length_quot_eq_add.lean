-- Prove2me | solution 1 for Formalism.G0.LengthLayersP.length_quot_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:41:45.52661+00:00
-- url     : https://prove2.me/submissions/5ac34773-b4dc-46ef-8e2d-701d630735b7

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
theorem _root_.solution {X : Type} [AddCommGroup X] [Module O X] {U V : Submodule O X}
    (h : U ≤ V) :
    Module.length O (X ⧸ U) = Module.length O ↥(V.map U.mkQ) + Module.length O (X ⧸ V) := by
  refine Module.length_eq_add_of_exact (V.map U.mkQ).subtype (U.mapQ V LinearMap.id (fun x hx => h hx))
    Subtype.val_injective ?_ ?_
  · intro y
    obtain ⟨x, rfl⟩ := V.mkQ_surjective y
    exact ⟨U.mkQ x, rfl⟩
  · intro y
    obtain ⟨x, rfl⟩ := U.mkQ_surjective y
    constructor
    · intro hx
      have hxV : x ∈ V := (Submodule.Quotient.mk_eq_zero V).mp hx
      exact ⟨⟨U.mkQ x, Submodule.mem_map_of_mem hxV⟩, rfl⟩
    · rintro ⟨⟨z, hz⟩, hzx⟩
      obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hz
      have h1 : U.mkQ w = U.mkQ x := hzx
      have h2 : w - x ∈ U := (Submodule.Quotient.eq U).mp h1
      have h3 : x ∈ V := by simpa using V.sub_mem hw (h h2)
      exact (Submodule.Quotient.mk_eq_zero V).mpr h3
end Formalism.G0.LengthLayersP
