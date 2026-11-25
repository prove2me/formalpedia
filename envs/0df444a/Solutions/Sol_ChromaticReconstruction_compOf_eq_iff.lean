-- Prove2me | solution 1 for ChromaticReconstruction.compOf_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:42:28.5268+00:00
-- url     : https://prove2.me/submissions/d36fdb59-cbcb-43fd-b99e-c124d8ce0f45

import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_Forest
import Theorems.Thm_ChromaticReconstruction_compOf_mem
import Theorems.Thm_ChromaticReconstruction_eq_of_mem_compSets
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_mem_compOf_self
attribute [local simp] ChromaticReconstruction.killP1_X_one



set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution {A : Set (Sym2 V)} {x y : V} :
    compOf A x = compOf A y ↔ (SimpleGraph.fromEdgeSet A).Reachable x y := by
  constructor
  · intro h
    have : y ∈ compOf A x := h ▸ mem_compOf_self A y
    simpa [compOf] using this
  · intro h
    exact eq_of_mem_compSets (compOf_mem A x) (compOf_mem A y)
      (by simpa [compOf] using h) (mem_compOf_self A y)
end ChromaticReconstruction
