-- Prove2me | solution 1 for ChromaticReconstruction.card_blk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:18:18.932352+00:00
-- url     : https://prove2.me/submissions/534656fb-041f-402c-8081-cfd5531688d2

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_LeafExtMaster
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inr
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inr
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
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
theorem _root_.solution (l0 : Σ i, Fin (m i)) (C : Finset K) :
    (blk m l0 C).card = (∑ i ∈ C, (m i + 1)) - if l0.1 ∈ C then 1 else 0 := by
  unfold blk
  rw [card_union_of_disjoint, card_map, card_map]
  · have h1 : (univ.filter fun l : Σ i, Fin (m i) => l.1 ∈ C) = C.sigma fun _ => univ := by
      ext l; simp
    have h2 : (univ.filter fun l : Σ i, Fin (m i) => l.1 ∈ C ∧ l ≠ l0) =
        (univ.filter fun l : Σ i, Fin (m i) => l.1 ∈ C).erase l0 := by
      ext l; simp [and_comm]
    rw [h2, h1, sum_add_distrib, sum_const, smul_eq_mul, mul_one]
    split_ifs with hC
    · rw [card_erase_of_mem (by simp [hC]), card_sigma]
      simp only [card_univ, Fintype.card_fin]
      have : 1 ≤ ∑ i ∈ C, m i :=
        le_trans (Fin.pos l0.2) (single_le_sum (f := m) (fun _ _ => Nat.zero_le _) hC)
      have hpos : 0 < C.card := card_pos.2 ⟨_, hC⟩
      omega
    · rw [erase_eq_of_notMem (by simp [hC]), card_sigma]
      simp [add_comm]
  · rw [disjoint_left]
    intro z hz hz'
    simp only [mem_map] at hz hz'
    obtain ⟨a, _, rfl⟩ := hz
    obtain ⟨b, _, hb⟩ := hz'
    simp at hb
end ChromaticReconstruction
