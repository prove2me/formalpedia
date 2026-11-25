-- Prove2me | solution 1 for DilworthTheorem.isChain_finset_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:33:03.626462+00:00
-- url     : https://prove2.me/submissions/3b5c8104-2d30-4b97-bba4-3ffcc8d2b7d4

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
import Theorems.Thm_DilworthTheorem_isChain_singleton

set_option autoImplicit true
open DilworthTheorem
open Finset
open Classical
variable {α : Type*} [PartialOrder α]
namespace DilworthTheorem
theorem _root_.solution (x : α) : IsChain (({x} : Finset α) : Set α) := by
  rw [coe_singleton]; exact isChain_singleton x
end DilworthTheorem
