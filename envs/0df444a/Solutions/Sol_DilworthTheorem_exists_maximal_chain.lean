-- Prove2me | solution 1 for DilworthTheorem.exists_maximal_chain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:36:06.898534+00:00
-- url     : https://prove2.me/submissions/5aa64ee9-2f2b-42f5-b958-07a89b7023cc

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Antichain
import Mathlib.Tactic
import Definitions.Def_StableMarriageF6_DilworthTheorem
import Theorems.Thm_DilworthTheorem_isChain_finset_singleton
import Theorems.Thm_DilworthTheorem_chain_has_max
import Theorems.Thm_DilworthTheorem_chain_has_min

set_option autoImplicit true
open DilworthTheorem
open Finset
open Classical
variable {α : Type*} [PartialOrder α]
namespace DilworthTheorem
theorem _root_.solution (S : Finset α) (hS : S.Nonempty) :
    ∃ C : Finset α, C ⊆ S ∧ C.Nonempty ∧ IsChain (C : Set α) ∧
      (∃ cmax ∈ C, ∀ x ∈ S, cmax ≤ x → x = cmax) ∧
      (∃ cmin ∈ C, ∀ x ∈ S, x ≤ cmin → x = cmin) := by
  rcases hS with ⟨x, hx⟩
  let F : Finset (Finset α) := S.powerset.filter (fun c => c.Nonempty ∧ IsChain (c : Set α))
  have hF_ne : F.Nonempty := ⟨{x}, mem_filter.mpr ⟨mem_powerset.mpr (singleton_subset_iff.mpr hx), singleton_nonempty x, isChain_finset_singleton x⟩⟩
  rcases Finset.exists_max_image F Finset.card hF_ne with ⟨C, hC_in, hC_max⟩
  simp only [mem_filter, mem_powerset, F] at hC_in
  rcases hC_in with ⟨hC_sub, hC_ne, hC_chain⟩
  rcases chain_has_max C hC_ne hC_chain with ⟨cmax, hcmax_in, hcmax_max⟩
  rcases chain_has_min C hC_ne hC_chain with ⟨cmin, hcmin_in, hcmin_min⟩
  refine ⟨C, hC_sub, hC_ne, hC_chain, ⟨cmax, hcmax_in, fun x0 hx0 hle => ?_⟩, ⟨cmin, hcmin_in, fun x0 hx0 hle => ?_⟩⟩
  · by_contra hne
    have hlt : cmax < x0 := lt_of_le_of_ne hle (Ne.symm hne)
    have hx_not : x0 ∉ C := fun h => (not_lt_of_ge (hcmax_max x0 h)) hlt
    have hC'_chain : IsChain ((insert x0 C : Finset α) : Set α) := by
      intro u v hu hv; simp only [mem_coe, mem_insert] at hu hv
      rcases hu with rfl | hu <;> rcases hv with rfl | hv
      · exact Or.inl le_rfl
      · exact Or.inr ((hcmax_max v hv).trans_lt hlt).le
      · exact Or.inl ((hcmax_max u hu).trans_lt hlt).le
      · exact hC_chain u v hu hv
    have hC'_in : insert x0 C ∈ F := mem_filter.mpr ⟨mem_powerset.mpr (insert_subset hx0 hC_sub), insert_nonempty x0 C, hC'_chain⟩
    have h_le := hC_max (insert x0 C) hC'_in
    rw [card_insert_of_notMem hx_not] at h_le; omega
  · by_contra hne
    have hlt : x0 < cmin := lt_of_le_of_ne hle hne
    have hx_not : x0 ∉ C := fun h => (not_lt_of_ge (hcmin_min x0 h)) hlt
    have hC'_chain : IsChain ((insert x0 C : Finset α) : Set α) := by
      intro u v hu hv; simp only [mem_coe, mem_insert] at hu hv
      rcases hu with rfl | hu <;> rcases hv with rfl | hv
      · exact Or.inl le_rfl
      · exact Or.inl (hlt.trans_le (hcmin_min v hv)).le
      · exact Or.inr (hlt.trans_le (hcmin_min u hu)).le
      · exact hC_chain u v hu hv
    have hC'_in : insert x0 C ∈ F := mem_filter.mpr ⟨mem_powerset.mpr (insert_subset hx0 hC_sub), insert_nonempty x0 C, hC'_chain⟩
    have h_le := hC_max (insert x0 C) hC'_in
    rw [card_insert_of_notMem hx_not] at h_le; omega
end DilworthTheorem
