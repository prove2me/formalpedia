-- Prove2me | solution 1 for ChromaticReconstruction.killP1_pderiv_typeMonomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:11:59.211586+00:00
-- url     : https://prove2.me/submissions/c642f980-2a9a-4507-b529-8b4e80352eae

import Definitions.Def_RequestProject_Components
import Definitions.Def_RequestProject_PhiFormula
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_pderiv_prod
attribute [local simp] ChromaticReconstruction.killP1_X_one

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution (A : Set (Sym2 V)) :
    killP1 (pderiv 1 (typeMonomial A)) =
      ∑ v, if {v} ∈ compSets A then killP1 (∏ D ∈ (compSets A).erase {v}, X D.card) else 0 := by
  unfold typeMonomial
  rw [pderiv_prod, map_sum]
  simp only [pderiv_X, Pi.single_apply, mul_ite, mul_one, mul_zero]
  simp_rw [apply_ite killP1, map_zero]
  rw [← sum_filter, ← sum_filter]
  symm
  refine sum_bij (fun v _ => {v}) ?_ ?_ ?_ ?_
  · intro v hv
    simp only [mem_filter, mem_univ, true_and] at hv
    simp [hv]
  · intro v _ w _ h
    exact singleton_injective h
  · intro C hC
    simp only [mem_filter] at hC
    obtain ⟨v, rfl⟩ := card_eq_one.1 hC.2
    exact ⟨v, by simp [hC.1], rfl⟩
  · intro v _
    convert rfl
end ChromaticReconstruction
