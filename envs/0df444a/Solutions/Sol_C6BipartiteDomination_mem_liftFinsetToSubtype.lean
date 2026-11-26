-- Prove2me | solution 1 for C6BipartiteDomination.mem_liftFinsetToSubtype
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:06:57.45725+00:00
-- url     : https://prove2.me/submissions/6d8fc8eb-b624-4287-9ce8-74dcd3a39bde

import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Definitions.Def_C6BipartiteDomination_MainResults

set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {S E : Finset V} (hES : E ⊆ S)
    (x : {v // v ∈ S}) :
    x ∈ liftFinsetToSubtype S E hES ↔ x.1 ∈ E := by
  classical
  change x ∈ E.attach.image
      (fun y => (⟨y.1, hES y.2⟩ : {v // v ∈ S})) ↔ x.1 ∈ E
  rw [Finset.mem_image]
  constructor
  · rintro ⟨y, hy, hEq⟩
    exact (congrArg Subtype.val hEq) ▸ y.2
  · intro hx
    refine ⟨⟨x.1, hx⟩, Finset.mem_attach _ _, ?_⟩
    exact Subtype.ext rfl
end C6BipartiteDomination
