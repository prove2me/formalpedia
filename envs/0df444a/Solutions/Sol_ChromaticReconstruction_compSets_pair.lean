-- Prove2me | solution 1 for ChromaticReconstruction.compSets_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:47:18.547797+00:00
-- url     : https://prove2.me/submissions/0c85626f-3b83-4b16-bc67-052734b02071

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_CompStructure
import Theorems.Thm_ChromaticReconstruction_compSets_eq_of_partition
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_reachable_of_mem
attribute [local simp] ChromaticReconstruction.killP1_X_one



set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution {u v : V} :
    compSets ({s(u, v)} : Set (Sym2 V)) =
      insert {u, v} ((univ \ {u, v}).image fun w => ({w} : Finset V)) := by
  apply compSets_eq_of_partition
  · intro w
    by_cases hw : w ∈ ({u, v} : Finset V)
    · exact ⟨_, mem_insert_self _ _, hw⟩
    · exact ⟨{w}, mem_insert_of_mem (mem_image.2 ⟨w, by simp [hw], rfl⟩), mem_singleton_self w⟩
  · intro B hB
    rcases mem_insert.1 hB with rfl | hB
    · simp
    · obtain ⟨w, _, rfl⟩ := mem_image.1 hB; simp
  · intro B hB x hx y hy
    rcases mem_insert.1 hB with rfl | hB
    · have huv' : (SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 V))).Reachable u v :=
        reachable_of_mem rfl
      simp only [mem_insert, mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · rfl
      · exact huv'
      · exact huv'.symm
      · rfl
    · obtain ⟨w, _, rfl⟩ := mem_image.1 hB
      simp only [mem_singleton] at hx hy
      rw [hx, hy]
  · intro B hB x hx y hy
    simp only [Set.mem_singleton_iff, Sym2.eq_iff] at hy
    rcases mem_insert.1 hB with rfl | hB
    · rcases hy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
    · obtain ⟨w, hw, rfl⟩ := mem_image.1 hB
      simp only [mem_singleton] at hx
      subst hx
      simp only [mem_sdiff, mem_univ, mem_insert, mem_singleton, true_and, not_or] at hw
      rcases hy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd rfl hw.1
      · exact absurd rfl hw.2
end ChromaticReconstruction
