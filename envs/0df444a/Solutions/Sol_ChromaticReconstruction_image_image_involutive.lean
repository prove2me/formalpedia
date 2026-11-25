-- Prove2me | solution 1 for ChromaticReconstruction.image_image_involutive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:30:23.33549+00:00
-- url     : https://prove2.me/submissions/bba7d1b7-8dbb-41e6-8b24-5beea1919113

import Definitions.Def_RequestProject_PathLeaf
import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_PathLeafSwap
import Theorems.Thm_ChromaticReconstruction_mem_image_involutive

set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {n c : ℕ}
namespace ChromaticReconstruction
theorem _root_.solution {α : Type*} [DecidableEq α] {f : α → α} (hf : Function.Involutive f)
    (F : Finset (Sym2 α)) : (F.image (Sym2.map f)).image (Sym2.map f) = F := by
  ext e
  rw [mem_image_involutive hf, mem_image_involutive hf, Sym2.map_map,
    show f ∘ f = id from funext hf, Sym2.map_id, id]
end ChromaticReconstruction
