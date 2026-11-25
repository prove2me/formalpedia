-- Prove2me | solution 1 for ChromaticReconstruction.card_key_fiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:53:41.268926+00:00
-- url     : https://prove2.me/submissions/b1d0015b-1b9a-437f-8f77-87f10a2a28df

import Definitions.Def_RequestProject_RecoveryThm
import Definitions.Def_RequestProject_WeightedIso
import Theorems.Thm_ChromaticReconstruction_sum_card_nbr_weight
import Theorems.Thm_ChromaticReconstruction_card_filter_weight
import Theorems.Thm_ChromaticReconstruction_degree_one_of_repeated
import Theorems.Thm_ChromaticReconstruction_unique_of_adj_leaf
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inr
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inr
import Theorems.Thm_ChromaticReconstruction_pairMS_mk
import Theorems.Thm_ChromaticReconstruction_pairSum_mk
import Theorems.Thm_ChromaticReconstruction_theta_mk
attribute [local simp] ChromaticReconstruction.killP1_X_one
attribute [local simp] ChromaticReconstruction.leafExt_adj_inl_inl
attribute [local simp] ChromaticReconstruction.leafExt_adj_inl_inr
attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inl
attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inr
attribute [local simp] ChromaticReconstruction.pairMS_mk
attribute [local simp] ChromaticReconstruction.pairSum_mk
attribute [local simp] ChromaticReconstruction.theta_mk



set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K]
variable {S : SimpleGraph K} {w : K → ℕ}
namespace ChromaticReconstruction
theorem _root_.solution (hS : S.Connected) (hk : 3 ≤ Fintype.card K) (hMI : MIso S w)
    (a : ℕ) (M : Multiset ℕ) :
    #{x | keyOf S w x = (a, M)} = fiberInv (wts w) (edgeTypes S w) a M := by
  unfold fiberInv
  split_ifs with hA hM hB
  · rw [← hA, ← card_filter_weight]
    congr 1
    ext x
    simp only [mem_filter, mem_univ, true_and, keyOf, Prod.mk.injEq, hM]
    constructor
    · exact fun h => h.1
    · intro hx; subst hx; simp [hA]
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro x _ hx
    simp only [keyOf, Prod.mk.injEq] at hx
    obtain ⟨rfl, hx⟩ := hx
    rw [if_pos hA] at hx
    exact hM hx.symm
  · obtain ⟨hMb, hba⟩ := hB
    rw [← sum_card_nbr_weight S w (Ne.symm hba)]
    have : (univ.filter fun x => keyOf S w x = (a, M)) =
        (univ.filter fun x => w x = a).filter
          fun x => (S.neighborFinset x).val.map w = {M.sum} := by
      ext x
      simp only [mem_filter, mem_univ, true_and, keyOf, Prod.mk.injEq]
      constructor
      · rintro ⟨rfl, h⟩
        rw [if_neg hA] at h
        exact ⟨rfl, h.trans hMb⟩
      · rintro ⟨rfl, h⟩
        rw [if_neg hA]
        exact ⟨rfl, h.trans hMb.symm⟩
    rw [this, card_filter]
    refine sum_congr rfl fun x hx => ?_
    simp only [mem_filter, mem_univ, true_and] at hx
    subst hx
    have hdeg := degree_one_of_repeated hMI hA
    obtain ⟨y, hy⟩ := card_eq_one.1
      ((S.card_neighborFinset_eq_degree x).trans hdeg)
    rw [hy, filter_singleton]
    simp only [singleton_val, Multiset.map_singleton, Multiset.singleton_inj]
    split_ifs <;> simp
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro x _ hx
    simp only [keyOf, Prod.mk.injEq] at hx
    obtain ⟨rfl, hx⟩ := hx
    rw [if_neg hA] at hx
    have hdeg := degree_one_of_repeated hMI hA
    obtain ⟨y, hy⟩ := card_eq_one.1
      ((S.card_neighborFinset_eq_degree x).trans hdeg)
    have hxy : S.Adj x y := (S.mem_neighborFinset x y).1 (by rw [hy]; exact mem_singleton_self y)
    have hyu := unique_of_adj_leaf hS hk hMI hdeg hxy
    rw [hy] at hx
    simp only [singleton_val, Multiset.map_singleton] at hx
    subst hx
    apply hB
    simp only [Multiset.sum_singleton, true_and]
    intro h
    rw [h] at hyu
    exact hA hyu
end ChromaticReconstruction
