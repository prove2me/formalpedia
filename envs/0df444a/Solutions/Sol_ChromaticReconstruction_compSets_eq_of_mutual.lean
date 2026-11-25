-- Prove2me | solution 1 for ChromaticReconstruction.compSets_eq_of_mutual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:18:00.339943+00:00
-- url     : https://prove2.me/submissions/8a564900-8092-4b29-a7c7-b27b1fbe6f38

import Definitions.Def_RequestProject_PathLeaf
import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_PathLeafSwap
import Theorems.Thm_ChromaticReconstruction_reachable_of_edges_reachable
import Theorems.Thm_ChromaticReconstruction_compSets_eq_image_compOf
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_vx_val
attribute [local simp] ChromaticReconstruction.killP1_X_one
attribute [local simp] ChromaticReconstruction.vx_val



set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {n c : ℕ}
variable {V : Type*} [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution {A B : Set (Sym2 V)}
    (hAB : ∀ u v, s(u, v) ∈ A → (SimpleGraph.fromEdgeSet B).Reachable u v)
    (hBA : ∀ u v, s(u, v) ∈ B → (SimpleGraph.fromEdgeSet A).Reachable u v) :
    compSets A = compSets B := by
  rw [compSets_eq_image_compOf, compSets_eq_image_compOf]
  congr 1
  funext x
  ext y
  simp only [compOf, mem_filter, mem_univ, true_and]
  exact ⟨reachable_of_edges_reachable hAB, reachable_of_edges_reachable hBA⟩
end ChromaticReconstruction
