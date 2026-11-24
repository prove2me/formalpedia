-- Prove2me | solution 1 for ChromaticReconstruction.edges_not_diag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T12:30:58.023589+00:00
-- url     : https://prove2.me/submissions/3cdffcf1-43b0-47a2-8d51-808befbec3dd

import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_Uniform
import Definitions.Def_RequestProject_ChromCoeff

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution (G : SimpleGraph V) {A : Finset (Sym2 V)} (hA : A ⊆ G.edgeFinset) :
    ∀ e ∈ A, ¬ e.IsDiag := by
  intro e he
  have := hA he
  rw [SimpleGraph.mem_edgeFinset] at this
  exact G.not_isDiag_of_mem_edgeSet this
end ChromaticReconstruction
