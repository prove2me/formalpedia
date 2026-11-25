-- Prove2me | solution 1 for ChromaticReconstruction.phiTerm_extEdges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:21:41.885104+00:00
-- url     : https://prove2.me/submissions/54330671-1cc6-4748-a275-3595d5cd9de3

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_LeafExtMaster
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inr
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inr
import Theorems.Thm_ChromaticReconstruction_compSets_extEdges
import Theorems.Thm_ChromaticReconstruction_card_extEdges
import Theorems.Thm_ChromaticReconstruction_blk_injective
import Theorems.Thm_ChromaticReconstruction_card_blk
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_nonempty_of_mem_compSets
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
    phiTerm (extEdges m l0 F) (.inr l0) =
      (-1) ^ ((∑ i, m i) - 1 + F.card) * killP1 (∏ C ∈ compSets (F : Set (Sym2 K)),
        X ((∑ i ∈ C, (m i + 1)) - if l0.1 ∈ C then 1 else 0)) := by
  unfold phiTerm
  rw [compSets_extEdges, if_pos (mem_insert_self _ _), card_extEdges]
  have hnot : ({Sum.inr l0} : Finset (K ⊕ Σ i, Fin (m i))) ∉
      (compSets (F : Set (Sym2 K))).image (blk m l0) := by
    intro h
    obtain ⟨C, hC, hCe⟩ := mem_image.1 h
    obtain ⟨i, hi⟩ := nonempty_of_mem_compSets hC
    have : (Sum.inl i : K ⊕ Σ i, Fin (m i)) ∈ blk m l0 C := by simp [blk, hi]
    rw [hCe] at this
    simp at this
  have he : (insert {Sum.inr l0} ((compSets (F : Set (Sym2 K))).image (blk m l0))).erase
      {Sum.inr l0} = (compSets (F : Set (Sym2 K))).image (blk m l0) := by
    convert erase_insert hnot
  have key : ∏ D ∈ (insert {Sum.inr l0} ((compSets (F : Set (Sym2 K))).image (blk m l0))).erase
      {Sum.inr l0}, (X D.card : MvPolynomial ℕ ℚ) = ∏ C ∈ compSets (F : Set (Sym2 K)),
        X ((∑ i ∈ C, (m i + 1)) - if l0.1 ∈ C then 1 else 0) := by
    rw [he, prod_image (fun C _ D _ h => blk_injective l0 h)]
    simp_rw [card_blk]
  convert congrArg (fun p => (-1) ^ ((∑ i, m i) - 1 + F.card) * killP1 p) key
end ChromaticReconstruction
