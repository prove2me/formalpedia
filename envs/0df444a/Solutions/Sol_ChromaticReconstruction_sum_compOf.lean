-- Prove2me | solution 1 for ChromaticReconstruction.sum_compOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:48:31.840968+00:00
-- url     : https://prove2.me/submissions/1ae078c9-a977-4c84-9fc3-17148772c142

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_CompStructure
import Theorems.Thm_ChromaticReconstruction_compOf_mem
import Theorems.Thm_ChromaticReconstruction_mem_compOf_self
import Theorems.Thm_ChromaticReconstruction_eq_compOf
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
attribute [local simp] ChromaticReconstruction.killP1_X_one



set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution {M : Type*} [AddCommMonoid M] (A : Set (Sym2 V)) (h : Finset V → M) :
    ∑ v, h (compOf A v) = ∑ C ∈ compSets A, C.card • h C := by
  rw [← sum_fiberwise_of_maps_to (s := univ) (t := compSets A) (g := compOf A)
    (fun v _ => compOf_mem A v)]
  refine sum_congr rfl fun C hC => ?_
  have : (univ.filter fun v => compOf A v = C) = C := by
    ext v
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro rfl; exact mem_compOf_self A v
    · intro hv; exact (eq_compOf hC hv).symm
  rw [sum_congr rfl (fun v hv => by rw [(mem_filter.1 hv).2]), sum_const, this]
end ChromaticReconstruction
