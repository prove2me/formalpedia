-- Prove2me | solution 1 for ChromaticReconstruction.singleton_mem_compSets_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:36:40.086278+00:00
-- url     : https://prove2.me/submissions/fc4bca2c-6950-4a9b-80dc-29678e567160

import Definitions.Def_RequestProject_Components
import Definitions.Def_RequestProject_PhiFormula
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_mem_compSets_of_reachable
import Theorems.Thm_ChromaticReconstruction_mem_of_reachable_of_closed
import Theorems.Thm_ChromaticReconstruction_reachable_of_mem

attribute [local simp] ChromaticReconstruction.killP1_X_one

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution (A : Set (Sym2 V)) (v : V) :
    {v} ∈ compSets A ↔ ∀ w, s(v, w) ∈ A → w = v := by
  constructor
  · intro h w hw
    have := mem_compSets_of_reachable h (mem_singleton_self v) (reachable_of_mem hw)
    simpa using this
  · intro h
    have : (univ.filter fun w => (SimpleGraph.fromEdgeSet A).Reachable v w) = {v} := by
      ext w
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · intro hr
        have := mem_of_reachable_of_closed (B := ({v} : Set V)) (fun u hu w hw => by
          simp only [Set.mem_singleton_iff] at hu ⊢
          subst hu; exact h w hw) rfl hr
        simpa using this
      · rintro rfl; rfl
    rw [← this]
    simp only [compSets, mem_image, mem_univ, true_and]
    exact ⟨v, rfl⟩
end ChromaticReconstruction
