-- Prove2me | solution 1 for DilworthTheorem.chain_has_max
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:30:52.302269+00:00
-- url     : https://prove2.me/submissions/363b917a-d268-4f69-92b9-4a16542df17e

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
import Theorems.Thm_DilworthTheorem_isChain_subset

set_option autoImplicit true
open DilworthTheorem
open Finset
open Classical
variable {α : Type*} [PartialOrder α]
namespace DilworthTheorem
theorem _root_.solution (C : Finset α) (hC_nonempty : C.Nonempty) (hC_chain : IsChain (C : Set α)) :
    ∃ m ∈ C, ∀ x ∈ C, x ≤ m := by
  induction' C using Finset.induction_on with a s ha ih
  · cases hC_nonempty.ne_empty rfl
  · rcases s.eq_empty_or_nonempty with rfl | hs
    · exact ⟨a, mem_singleton_self a, by simp⟩
    · rcases ih hs (isChain_subset (subset_insert a s) hC_chain) with ⟨m, hm, hm_max⟩
      rcases hC_chain a m (mem_insert_self a s) (mem_insert_of_mem hm) with h | h
      · exact ⟨m, mem_insert_of_mem hm, fun x hx => (mem_insert.mp hx).elim (fun e => e ▸ h) (hm_max x)⟩
      · exact ⟨a, mem_insert_self a s, fun x hx => (mem_insert.mp hx).elim (fun e => e ▸ le_rfl) (fun hx => (hm_max x hx).trans h)⟩
end DilworthTheorem
