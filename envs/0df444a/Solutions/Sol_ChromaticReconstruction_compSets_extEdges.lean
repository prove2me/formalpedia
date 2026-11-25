-- Prove2me | solution 1 for ChromaticReconstruction.compSets_extEdges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:16:53.214952+00:00
-- url     : https://prove2.me/submissions/2a19b957-652c-43d0-ad4d-36a4614def8c

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_LeafExtMaster
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inr
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inr
import Theorems.Thm_ChromaticReconstruction_mem_extEdges_inl_inl
import Theorems.Thm_ChromaticReconstruction_mem_extEdges_inl_inr
import Theorems.Thm_ChromaticReconstruction_mem_extEdges_inr_inl
import Theorems.Thm_ChromaticReconstruction_not_mem_extEdges_inr_inr
import Theorems.Thm_ChromaticReconstruction_compSets_eq_of_partition
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_mem_compSets_of_reachable
import Theorems.Thm_ChromaticReconstruction_mem_compSets_self
import Theorems.Thm_ChromaticReconstruction_nonempty_of_mem_compSets
import Theorems.Thm_ChromaticReconstruction_reachable_map
import Theorems.Thm_ChromaticReconstruction_reachable_of_mem
import Theorems.Thm_ChromaticReconstruction_reachable_of_mem_compSets
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
    compSets (extEdges m l0 F : Set (Sym2 (K ⊕ Σ i, Fin (m i)))) =
      insert {.inr l0} ((compSets (F : Set (Sym2 K))).image (blk m l0)) := by
  apply compSets_eq_of_partition
  · rintro (i | l)
    · obtain ⟨C, hC, hi⟩ := mem_compSets_self (F : Set (Sym2 K)) i
      exact ⟨blk m l0 C, mem_insert_of_mem (mem_image_of_mem _ hC), by simp [blk, hi]⟩
    · by_cases hl : l = l0
      · exact ⟨_, mem_insert_self _ _, by simp [hl]⟩
      · obtain ⟨C, hC, hi⟩ := mem_compSets_self (F : Set (Sym2 K)) l.1
        exact ⟨blk m l0 C, mem_insert_of_mem (mem_image_of_mem _ hC), by simp [blk, hi, hl]⟩
  · intro B hB
    rcases mem_insert.1 hB with rfl | hB
    · simp
    · obtain ⟨C, hC, rfl⟩ := mem_image.1 hB
      obtain ⟨i, hi⟩ := nonempty_of_mem_compSets hC
      exact ⟨.inl i, by simp [blk, hi]⟩
  · intro B hB
    rcases mem_insert.1 hB with rfl | hB
    · intro u hu w hw
      simp only [mem_singleton] at hu hw
      rw [hu, hw]
    · obtain ⟨C, hC, rfl⟩ := mem_image.1 hB
      -- every vertex of the block is reachable from a base vertex of the block
      have hbase : ∀ i ∈ C, ∀ j ∈ C,
          (SimpleGraph.fromEdgeSet ((extEdges m l0 F : Finset _) :
            Set (Sym2 (K ⊕ Σ i, Fin (m i))))).Reachable (Sum.inl i) (Sum.inl j) := by
        intro i hi j hj
        refine reachable_map Sum.inl _ _ (fun a b hab _ => Or.inr ?_)
          (reachable_of_mem_compSets hC hi hj)
        exact mem_extEdges_inl_inl.2 hab
      have hto : ∀ u ∈ blk m l0 C, ∃ i ∈ C,
          (SimpleGraph.fromEdgeSet ((extEdges m l0 F : Finset _) :
            Set (Sym2 (K ⊕ Σ i, Fin (m i))))).Reachable u (Sum.inl i) := by
        intro u hu
        simp only [blk, mem_union, mem_map, Function.Embedding.inl_apply,
          Function.Embedding.inr_apply, mem_filter, mem_univ, true_and] at hu
        rcases hu with ⟨i, hi, rfl⟩ | ⟨l, ⟨hlC, hl⟩, rfl⟩
        · exact ⟨i, hi, SimpleGraph.Reachable.refl _⟩
        · exact ⟨l.1, hlC, reachable_of_mem (mem_extEdges_inr_inl.2 ⟨rfl, hl⟩)⟩
      intro u hu w hw
      obtain ⟨i, hi, hui⟩ := hto u hu
      obtain ⟨j, hj, hwj⟩ := hto w hw
      exact hui.trans ((hbase i hi j hj).trans hwj.symm)
  · intro B hB
    rcases mem_insert.1 hB with rfl | hB
    · intro u hu w hw
      simp only [mem_singleton] at hu
      subst hu
      rcases w with a | l
      · exact absurd hw (by rw [mem_coe, mem_extEdges_inr_inl]; simp)
      · exact absurd hw not_mem_extEdges_inr_inr
    · obtain ⟨C, hC, rfl⟩ := mem_image.1 hB
      intro u hu w hw
      rw [mem_coe] at hw
      simp only [blk, mem_union, mem_map, Function.Embedding.inl_apply,
        Function.Embedding.inr_apply, mem_filter, mem_univ, true_and] at hu ⊢
      rcases hu with ⟨i, hi, rfl⟩ | ⟨l, ⟨hlC, hl⟩, rfl⟩
      · rcases w with b | l
        · rw [mem_extEdges_inl_inl] at hw
          exact Or.inl ⟨b, mem_compSets_of_reachable hC hi (reachable_of_mem hw), rfl⟩
        · rw [mem_extEdges_inl_inr] at hw
          exact Or.inr ⟨l, ⟨hw.1 ▸ hi, hw.2⟩, rfl⟩
      · rcases w with b | l'
        · rw [mem_extEdges_inr_inl] at hw
          exact Or.inl ⟨b, hw.1 ▸ hlC, rfl⟩
        · exact absurd hw not_mem_extEdges_inr_inr
end ChromaticReconstruction
