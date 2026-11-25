-- Prove2me | solution 1 for ChromaticReconstruction.exists_not_leaf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:10:21.517593+00:00
-- url     : https://prove2.me/submissions/2310adc8-964d-474d-9154-5be69964e78c

import Definitions.Def_RequestProject_WeightedIso
import Definitions.Def_RequestProject_ProperTree

set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V] {T : SimpleGraph V}
namespace ChromaticReconstruction
theorem _root_.solution (hT : IsProperTree T) : ∃ v, ¬ IsLeaf T v := by
  have : Nonempty V := Fintype.card_pos_iff.1 (by have := hT.2.1; omega)
  obtain ⟨v⟩ := this
  by_cases hv : IsLeaf T v
  · obtain ⟨c, hc⟩ := exists_adj_of_leaf hv
    exact ⟨c, not_leaf_of_adj_leaf hT hv hc⟩
  · exact ⟨v, hv⟩
end ChromaticReconstruction
