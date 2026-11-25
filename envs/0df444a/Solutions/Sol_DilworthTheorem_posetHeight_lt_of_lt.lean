-- Prove2me | solution 1 for DilworthTheorem.posetHeight_lt_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:41:38.410496+00:00
-- url     : https://prove2.me/submissions/5bdba615-62c3-41f3-b3e4-20e3d4e0dc69

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
import Theorems.Thm_DilworthTheorem_chainsEndingAt_nonempty

set_option autoImplicit true
open DilworthTheorem
open Finset
open Classical
variable {α : Type*} [PartialOrder α]
namespace DilworthTheorem
theorem _root_.solution {S : Finset α} {x y : α} (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) :
    posetHeight S x < posetHeight S y := by
  rcases Finset.exists_max_image (chainsEndingAt S x) Finset.card (chainsEndingAt_nonempty hx) with ⟨C, hC_in, hC_max⟩
  have hC_height : C.card = posetHeight S x := le_antisymm (Finset.le_sup hC_in) (Finset.sup_le hC_max)
  rw [chainsEndingAt, mem_filter, mem_powerset] at hC_in
  rcases hC_in with ⟨hCS, -, hC_le_x, hC_chain⟩
  have hy_not : y ∉ C := fun h => (not_lt_of_ge (hC_le_x y h)) hxy
  have hC'_chain : IsChain ((insert y C : Finset α) : Set α) := by
    intro u v hu hv; simp only [mem_coe, mem_insert] at hu hv
    rcases hu with rfl | hu <;> rcases hv with rfl | hv
    · exact Or.inl le_rfl
    · exact Or.inr ((hC_le_x v hv).trans hxy.le)
    · exact Or.inl ((hC_le_x u hu).trans hxy.le)
    · exact hC_chain u v hu hv
  have hC'_in : insert y C ∈ chainsEndingAt S y := by
    rw [chainsEndingAt, mem_filter, mem_powerset]
    refine ⟨insert_subset hy hCS, mem_insert_self y C, fun z hz => ?_, hC'_chain⟩
    exact (mem_insert.mp hz).elim (fun e => e ▸ le_rfl) (fun hz => (hC_le_x z hz).trans hxy.le)
  have h_le : (insert y C).card ≤ posetHeight S y := Finset.le_sup (f := Finset.card) hC'_in
  rw [card_insert_of_notMem hy_not, hC_height] at h_le; omega
end DilworthTheorem
