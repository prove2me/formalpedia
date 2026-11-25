-- Prove2me | solution 1 for DilworthTheorem.singleton_mem_chainsEndingAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:35:44.153799+00:00
-- url     : https://prove2.me/submissions/f278a163-a225-4b47-a9d8-97c25e90a390

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

set_option autoImplicit true
open DilworthTheorem
open Finset
open Classical
variable {α : Type*} [PartialOrder α]
namespace DilworthTheorem
theorem _root_.solution {S : Finset α} {x : α} (hx : x ∈ S) :
    {x} ∈ chainsEndingAt S x := by
  rw [chainsEndingAt, mem_filter, mem_powerset, singleton_subset_iff]
  exact ⟨hx, mem_singleton_self x, fun y hy => (mem_singleton.mp hy).le, isChain_finset_singleton x⟩
end DilworthTheorem
