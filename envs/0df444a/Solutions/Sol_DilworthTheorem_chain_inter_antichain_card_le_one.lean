-- Prove2me | solution 1 for DilworthTheorem.chain_inter_antichain_card_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:45:19.24587+00:00
-- url     : https://prove2.me/submissions/06fce590-5d5d-419f-aa63-fe8fb9898301

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
import Theorems.Thm_DilworthTheorem_chain_inter_antichain_subsingleton

set_option autoImplicit true
open DilworthTheorem
open Finset
open Classical
variable {α : Type*} [PartialOrder α]
namespace DilworthTheorem
theorem _root_.solution (C A : Finset α) (hC : IsChain (C : Set α)) (hA : IsAntichain (A : Set α)) :
    (C ∩ A).card ≤ 1 := by
  rw [card_le_one_iff]; intro a b ha hb
  exact chain_inter_antichain_subsingleton (C : Set α) (A : Set α) hC hA a b (mem_inter.mp ha) (mem_inter.mp hb)
end DilworthTheorem
