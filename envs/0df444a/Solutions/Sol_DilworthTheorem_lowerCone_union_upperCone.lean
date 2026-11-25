-- Prove2me | solution 1 for DilworthTheorem.lowerCone_union_upperCone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:32:37.619102+00:00
-- url     : https://prove2.me/submissions/1383e521-f822-4ede-927c-4676977035a0

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

set_option autoImplicit true
open DilworthTheorem
open Finset
open Classical
variable {α : Type*} [PartialOrder α]
namespace DilworthTheorem
theorem _root_.solution (S A : Finset α) (k : ℕ)
    (hAS : A ⊆ S) (hA_anti : IsAntichain (A : Set α)) (hA_card : A.card = k)
    (h_bound : ∀ B ⊆ S, IsAntichain (B : Set α) → B.card ≤ k) :
    lowerCone S A ∪ upperCone S A = S := by
  ext x; simp only [mem_union, lowerCone, upperCone, mem_filter]
  refine ⟨by rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx, fun hx => ?_⟩
  simp only [hx, true_and]; by_contra! h_not
  have hB_anti : IsAntichain ((insert x A : Finset α) : Set α) := by
    intro u v hu hv hne; simp only [mem_coe, mem_insert] at hu hv
    rcases hu with rfl | hu <;> rcases hv with rfl | hv
    · exact (hne rfl).elim
    · exact ⟨h_not.1 v hv, h_not.2 v hv⟩
    · exact ⟨h_not.2 u hu, h_not.1 u hu⟩
    · exact hA_anti u v hu hv hne
  have hB_card := h_bound (insert x A) (insert_subset hx hAS) hB_anti
  have hx_not : x ∉ A := fun h => h_not.1 x h le_rfl
  rw [card_insert_of_notMem hx_not, hA_card] at hB_card; omega
end DilworthTheorem
