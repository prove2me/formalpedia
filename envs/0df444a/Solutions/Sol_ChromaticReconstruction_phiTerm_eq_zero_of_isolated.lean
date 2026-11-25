-- Prove2me | solution 1 for ChromaticReconstruction.phiTerm_eq_zero_of_isolated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:15:37.007599+00:00
-- url     : https://prove2.me/submissions/d6fd18ac-9dfd-4d1e-9583-20f1a2ba871d

import Definitions.Def_RequestProject_Components
import Definitions.Def_RequestProject_PhiFormula
import Theorems.Thm_ChromaticReconstruction_killP1_prod_eq_zero_of_mem

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution {A : Finset (Sym2 V)} {u v : V} (huv : u ≠ v)
    (hu : {u} ∈ compSets (A : Set (Sym2 V))) : phiTerm A v = 0 := by
  unfold phiTerm
  split_ifs with h
  · rw [killP1_prod_eq_zero_of_mem (u := u), mul_zero]
    exact mem_erase.2 ⟨fun h' => huv (singleton_injective h'), hu⟩
  · rfl
end ChromaticReconstruction
