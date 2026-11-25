-- Prove2me | solution 1 for ChromaticReconstruction.compType_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:15:21.665356+00:00
-- url     : https://prove2.me/submissions/26760507-3514-4b9f-92ca-8a26482a44e8

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_CompStructure
import Theorems.Thm_ChromaticReconstruction_compSets_pair
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
attribute [local simp] ChromaticReconstruction.killP1_X_one



set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution {u v : V} (huv : u ≠ v) :
    compType ({s(u, v)} : Set (Sym2 V)) = 2 ::ₘ Multiset.replicate (Fintype.card V - 2) 1 := by
  have hP := compSets_pair (u := u) (v := v)
  have hnot : ({u, v} : Finset V) ∉ (univ \ {u, v}).image fun w => ({w} : Finset V) := by
    intro h
    obtain ⟨w, hw, hwe⟩ := mem_image.1 h
    have : u ∈ ({w} : Finset V) := hwe ▸ mem_insert_self u {v}
    have h2 : v ∈ ({w} : Finset V) := hwe ▸ mem_insert_of_mem (mem_singleton_self v)
    simp only [mem_singleton] at this h2
    exact huv (this.trans h2.symm)
  rw [compType, hP, insert_val_of_notMem hnot, Multiset.map_cons, card_pair huv]
  congr 1
  rw [image_val_of_injOn (fun a _ b _ h => singleton_injective h), Multiset.map_map]
  simp only [Function.comp_def, card_singleton, Multiset.map_const', card_val, card_sdiff,
    card_univ]
  rw [inter_eq_left.2 (subset_univ _), card_pair huv]
end ChromaticReconstruction
