-- Prove2me | solution 1 for DilworthTheorem.chainsEndingAt_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:38:32.40118+00:00
-- url     : https://prove2.me/submissions/7a0aa49d-61a6-406f-adfd-caab0e317303

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
    (chainsEndingAt S x).Nonempty :=
  ⟨{x}, singleton_mem_chainsEndingAt hx⟩
end DilworthTheorem
