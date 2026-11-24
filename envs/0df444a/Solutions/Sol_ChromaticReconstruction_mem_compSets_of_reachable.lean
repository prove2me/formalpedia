-- Prove2me | solution 1 for ChromaticReconstruction.mem_compSets_of_reachable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:08:09.017362+00:00
-- url     : https://prove2.me/submissions/626c3678-1d4d-4f3b-895d-fcc020e5a3cf

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
theorem _root_.solution {A : Set (Sym2 V)} {C : Finset V} (hC : C ∈ compSets A)
    {u w : V} (hu : u ∈ C) (huw : (SimpleGraph.fromEdgeSet A).Reachable u w) : w ∈ C := by
  simp only [compSets, mem_image, mem_univ, true_and] at hC
  obtain ⟨v, rfl⟩ := hC
  simp only [mem_filter, mem_univ, true_and] at hu ⊢
  exact hu.trans huw
end ChromaticReconstruction
