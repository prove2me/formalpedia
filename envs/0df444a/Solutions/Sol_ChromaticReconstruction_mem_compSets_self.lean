-- Prove2me | solution 1 for ChromaticReconstruction.mem_compSets_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:42:33.587198+00:00
-- url     : https://prove2.me/submissions/8d340c2f-e5a4-4967-9157-27c9bda22ec1

import Definitions.Def_RequestProject_Defs
import Definitions.Def_RequestProject_Components

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V W : Type*}
variable [Fintype V] [Fintype W]
namespace ChromaticReconstruction
theorem _root_.solution (A : Set (Sym2 V)) (v : V) :
    ∃ C ∈ compSets A, v ∈ C := by
  refine ⟨univ.filter fun w => (SimpleGraph.fromEdgeSet A).Reachable v w, ?_, ?_⟩
  · simp only [compSets, mem_image, mem_univ, true_and]
    exact ⟨v, rfl⟩
  · simp
end ChromaticReconstruction
