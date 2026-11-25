-- Prove2me | solution 1 for DilworthTheorem.posetHeight_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:38:48.688796+00:00
-- url     : https://prove2.me/submissions/92e28e22-73b7-45e9-b8cd-99b0d784cc75

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
import Theorems.Thm_DilworthTheorem_singleton_mem_chainsEndingAt

set_option autoImplicit true
open DilworthTheorem
open Finset
open Classical
variable {α : Type*} [PartialOrder α]
namespace DilworthTheorem
theorem _root_.solution {S : Finset α} {x : α} (hx : x ∈ S) :
    1 ≤ posetHeight S x := by
  have := Finset.le_sup (f := Finset.card) (singleton_mem_chainsEndingAt hx)
  rwa [card_singleton] at this
end DilworthTheorem
