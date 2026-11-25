-- Prove2me | solution 1 for ChromaticReconstruction.prod_compSets_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:12:15.828648+00:00
-- url     : https://prove2.me/submissions/62800ef2-d76a-437a-b486-adbd6673dbd9

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_CompStructure
import Theorems.Thm_ChromaticReconstruction_compOf_mem
import Theorems.Thm_ChromaticReconstruction_mem_compOf_self
import Theorems.Thm_ChromaticReconstruction_eq_compOf

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution {M : Type*} [CommMonoid M] (A : Set (Sym2 V)) (v : V)
    (f g : Finset V → M) :
    ∏ C ∈ compSets A, (if v ∈ C then g C else f C) =
      g (compOf A v) * ∏ C ∈ (compSets A).erase (compOf A v), f C := by
  rw [← mul_prod_erase _ _ (compOf_mem A v), if_pos (mem_compOf_self A v)]
  congr 1
  refine prod_congr rfl fun C hC => ?_
  rw [if_neg]
  intro hv
  exact (mem_erase.1 hC).1 (eq_compOf (mem_erase.1 hC).2 hv)
end ChromaticReconstruction
