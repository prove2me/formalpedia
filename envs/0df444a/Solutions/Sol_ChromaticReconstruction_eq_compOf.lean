-- Prove2me | solution 1 for ChromaticReconstruction.eq_compOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:42:05.274876+00:00
-- url     : https://prove2.me/submissions/377e5afc-dc6c-49c8-aff0-54bc47d4881f

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_CompStructure
import Theorems.Thm_ChromaticReconstruction_compOf_mem
import Theorems.Thm_ChromaticReconstruction_mem_compOf_self
import Theorems.Thm_ChromaticReconstruction_eq_of_mem_compSets


set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution {A : Set (Sym2 V)} {C : Finset V} (hC : C ∈ compSets A) {v : V} (hv : v ∈ C) :
    C = compOf A v :=
  eq_of_mem_compSets hC (compOf_mem A v) hv (mem_compOf_self A v)
end ChromaticReconstruction
