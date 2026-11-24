-- Prove2me | solution 1 for ChromaticReconstruction.eq_of_mem_compSets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:45:23.203381+00:00
-- url     : https://prove2.me/submissions/47db26f8-8c18-43de-9d27-f390bbbdc444

import Definitions.Def_RequestProject_Defs
import Definitions.Def_RequestProject_Components
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
theorem _root_.solution {A : Set (Sym2 V)} {C D : Finset V} (hC : C ∈ compSets A)
    (hD : D ∈ compSets A) {v : V} (hvC : v ∈ C) (hvD : v ∈ D) : C = D := by
  ext w
  constructor
  · intro hw
    exact mem_compSets_of_reachable hD hvD (reachable_of_mem_compSets hC hvC hw)
  · intro hw
    exact mem_compSets_of_reachable hC hvC (reachable_of_mem_compSets hD hvD hw)
end ChromaticReconstruction
