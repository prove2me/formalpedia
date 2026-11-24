-- Prove2me | solution 1 for ChromaticReconstruction.compSets_map_equiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:52:42.717065+00:00
-- url     : https://prove2.me/submissions/6081ade4-5583-4e3f-9e7e-944e1d75e70c

import Definitions.Def_RequestProject_Defs
import Definitions.Def_RequestProject_Components
import Theorems.Thm_ChromaticReconstruction_reachable_map
import Theorems.Thm_ChromaticReconstruction_reachable_of_mem
import Theorems.Thm_ChromaticReconstruction_compSets_eq_of_partition
import Theorems.Thm_ChromaticReconstruction_mem_compSets_self
import Theorems.Thm_ChromaticReconstruction_nonempty_of_mem_compSets
import Theorems.Thm_ChromaticReconstruction_reachable_of_mem_compSets
import Theorems.Thm_ChromaticReconstruction_mem_compSets_of_reachable

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V W : Type*}
variable [Fintype V] [Fintype W]
namespace ChromaticReconstruction
theorem _root_.solution (e : V ≃ W) (A : Set (Sym2 V)) :
    compSets (Sym2.map e '' A) = (compSets A).image (Finset.map e.toEmbedding) := by
  have hfwd : ∀ {u v : V}, (SimpleGraph.fromEdgeSet A).Reachable u v →
      (SimpleGraph.fromEdgeSet (Sym2.map e '' A)).Reachable (e u) (e v) := by
    intro u v h
    exact reachable_map e A _ (fun a b hab _ => Or.inr (by
      simpa using Set.mem_image_of_mem (Sym2.map e) hab)) h
  have hbwd : ∀ {u v : W}, (SimpleGraph.fromEdgeSet (Sym2.map e '' A)).Reachable u v →
      (SimpleGraph.fromEdgeSet A).Reachable (e.symm u) (e.symm v) := by
    intro u v h
    refine reachable_map e.symm _ A (fun a b hab _ => Or.inr ?_) h
    obtain ⟨z, hz, hze⟩ := hab
    have : s(e.symm a, e.symm b) = z := by
      have := congrArg (Sym2.map e.symm) hze
      simpa [Sym2.map_map] using this.symm
    exact this ▸ hz
  apply compSets_eq_of_partition
  · intro w
    obtain ⟨C, hC, hv⟩ := mem_compSets_self A (e.symm w)
    exact ⟨_, mem_image_of_mem _ hC, by simpa using hv⟩
  · intro B hB
    obtain ⟨C, hC, rfl⟩ := mem_image.1 hB
    exact (nonempty_of_mem_compSets hC).map
  · intro B hB u hu w hw
    obtain ⟨C, hC, rfl⟩ := mem_image.1 hB
    simp only [mem_map_equiv] at hu hw
    have := hfwd (reachable_of_mem_compSets hC hu hw)
    simpa using this
  · intro B hB u hu w hw
    obtain ⟨C, hC, rfl⟩ := mem_image.1 hB
    simp only [mem_map_equiv] at hu ⊢
    exact mem_compSets_of_reachable hC hu (hbwd (reachable_of_mem hw))
end ChromaticReconstruction
