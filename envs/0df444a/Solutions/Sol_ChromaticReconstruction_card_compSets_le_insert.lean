-- Prove2me | solution 1 for ChromaticReconstruction.card_compSets_le_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:31:31.629806+00:00
-- url     : https://prove2.me/submissions/292728c0-55f5-4dfe-a7d1-fa7d77eff137

import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_Forest
import Theorems.Thm_ChromaticReconstruction_compSets_eq_image_compOf
import Theorems.Thm_ChromaticReconstruction_compOf_insert_eq
import Theorems.Thm_ChromaticReconstruction_biUnion_compOf
import Theorems.Thm_ChromaticReconstruction_compOf_mem
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
attribute [local simp] ChromaticReconstruction.killP1_X_one



set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution (A : Set (Sym2 V)) (e : Sym2 V) :
    (compSets A).card ≤ (compSets (insert e A)).card + 1 := by
  induction e using Sym2.ind with
  | _ u v =>
  have h1 : (compSets A).card ≤ ((compSets A).erase (compOf A v)).card + 1 := by
    rw [card_erase_of_mem (compOf_mem A v)]; omega
  have h2 : ((compSets A).erase (compOf A v)).card ≤ (compSets (insert s(u, v) A)).card := by
    apply card_le_card_of_injOn (fun C => C.biUnion (compOf (insert s(u, v) A)))
    · intro C hC
      have hC' := mem_of_mem_erase hC
      rw [compSets_eq_image_compOf] at hC'
      obtain ⟨x, -, rfl⟩ := mem_image.1 hC'
      rw [coe_erase] at *
      simp only [Set.mem_diff] at *
      rw [biUnion_compOf (Set.subset_insert _ _)]
      exact compOf_mem _ x
    · intro C hC D hD hCD
      simp only [coe_erase, Set.mem_diff, mem_coe, Set.mem_singleton_iff] at hC hD
      rw [compSets_eq_image_compOf] at hC hD
      obtain ⟨⟨x, -, rfl⟩, hx⟩ := And.imp_left mem_image.1 hC
      obtain ⟨⟨y, -, rfl⟩, hy⟩ := And.imp_left mem_image.1 hD
      simp only at hCD
      rw [biUnion_compOf (Set.subset_insert _ _), biUnion_compOf (Set.subset_insert _ _)] at hCD
      rcases compOf_insert_eq hCD with h | ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h hy
      · exact absurd h hx
  omega
end ChromaticReconstruction
