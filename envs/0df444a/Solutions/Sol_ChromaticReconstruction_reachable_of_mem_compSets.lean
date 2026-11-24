-- Prove2me | solution 1 for ChromaticReconstruction.reachable_of_mem_compSets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:14:49.050881+00:00
-- url     : https://prove2.me/submissions/02681e88-4caa-4c12-a767-71a22a391a3f

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
    {u w : V} (hu : u ∈ C) (hw : w ∈ C) : (SimpleGraph.fromEdgeSet A).Reachable u w := by
  simp only [compSets, mem_image, mem_univ, true_and] at hC
  obtain ⟨v, rfl⟩ := hC
  simp only [mem_filter, mem_univ, true_and] at hu hw
  exact hu.symm.trans hw
end ChromaticReconstruction
