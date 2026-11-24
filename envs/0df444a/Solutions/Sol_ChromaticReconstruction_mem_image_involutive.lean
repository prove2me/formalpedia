-- Prove2me | solution 1 for ChromaticReconstruction.mem_image_involutive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T14:41:25.142027+00:00
-- url     : https://prove2.me/submissions/ffe3ca19-7652-4400-b0ba-b1eb114ddbbd

import Definitions.Def_RequestProject_PathLeaf
import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_PathLeafSwap

set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {n c : ℕ}
namespace ChromaticReconstruction
theorem _root_.solution {α : Type*} [DecidableEq α] {f : α → α} (hf : Function.Involutive f)
    (F : Finset (Sym2 α)) (e : Sym2 α) : e ∈ F.image (Sym2.map f) ↔ Sym2.map f e ∈ F := by
  constructor
  · rintro h
    obtain ⟨e', he', rfl⟩ := mem_image.1 h
    rwa [Sym2.map_map, show f ∘ f = id from funext hf, Sym2.map_id, id]
  · intro h
    exact mem_image.2 ⟨_, h, by rw [Sym2.map_map, show f ∘ f = id from funext hf, Sym2.map_id, id]⟩
end ChromaticReconstruction
