-- Prove2me | solution 1 for ChromaticReconstruction.phiTerm_inl_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:22:41.666973+00:00
-- url     : https://prove2.me/submissions/381342cf-5b58-430d-9980-f26f05b16acf

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_LeafExtMaster
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inr
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inr
import Theorems.Thm_ChromaticReconstruction_singleton_inr_mem_compSets
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_phiTerm_eq_zero_of_isolated
import Theorems.Thm_ChromaticReconstruction_singleton_mem_compSets_iff
attribute [local simp] ChromaticReconstruction.killP1_X_one


attribute [local simp] ChromaticReconstruction.leafExt_adj_inl_inl
attribute [local simp] ChromaticReconstruction.leafExt_adj_inl_inr
attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inl
attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inr

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K] (S : SimpleGraph K) (m : K → ℕ)
variable {S m}
namespace ChromaticReconstruction
theorem _root_.solution (hm : ∀ i, 1 ≤ m i) {A : Finset (Sym2 (K ⊕ Σ i, Fin (m i)))}
    (hA : A ⊆ (leafExt S m).edgeFinset) (i : K) : phiTerm A (.inl i) = 0 := by
  by_cases hi : {.inl i} ∈ compSets (A : Set (Sym2 (K ⊕ Σ i, Fin (m i))))
  · let l : Σ i, Fin (m i) := ⟨i, ⟨0, hm i⟩⟩
    have hl : leafEdge m l ∉ A := by
      intro h
      rw [singleton_mem_compSets_iff] at hi
      have := hi (.inr l) (by exact h)
      simp at this
    exact phiTerm_eq_zero_of_isolated (by simp) (singleton_inr_mem_compSets hA hl)
  · unfold phiTerm; rw [if_neg hi]
end ChromaticReconstruction
