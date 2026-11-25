-- Prove2me | solution 1 for ChromaticReconstruction.card_extEdges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:18:11.490709+00:00
-- url     : https://prove2.me/submissions/8580e6ac-a463-42e7-a988-aa7cde0322f6

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_LeafExtMaster
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inr
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inr
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
attribute [local simp] ChromaticReconstruction.killP1_X_one


attribute [local simp] ChromaticReconstruction.leafExt_adj_inl_inl
attribute [local simp] ChromaticReconstruction.leafExt_adj_inl_inr
attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inl
attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inr

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K] (S : SimpleGraph K) (m : K → ℕ)
variable {S m}
namespace ChromaticReconstruction
theorem _root_.solution (l0 : Σ i, Fin (m i)) (F : Finset (Sym2 K)) :
    (extEdges m l0 F).card = (∑ i, m i) - 1 + F.card := by
  unfold extEdges
  rw [card_union_of_disjoint, card_image_of_injective, card_map, card_erase_of_mem (mem_univ _),
    card_univ, Fintype.card_sigma]
  · simp
  · intro l l' h
    simp only [leafEdge, Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, and_false,
      or_false] at h
    exact h.2
  · rw [disjoint_left]
    intro z hz hz'
    simp only [mem_image, mem_erase, mem_univ, and_true, mem_map] at hz hz'
    obtain ⟨l, _, rfl⟩ := hz
    obtain ⟨e, _, he⟩ := hz'
    induction e using Sym2.ind with
    | _ a b => simp [leafEdge] at he
end ChromaticReconstruction
