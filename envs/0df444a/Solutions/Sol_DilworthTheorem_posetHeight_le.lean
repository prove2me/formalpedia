-- Prove2me | solution 1 for DilworthTheorem.posetHeight_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:35:14.639945+00:00
-- url     : https://prove2.me/submissions/67155b64-e973-4172-a10f-e67e6951cc66

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
theorem _root_.solution {S : Finset α} {x : α} {m : ℕ}
    (h_chain : ∀ C ⊆ S, IsChain (C : Set α) → C.card ≤ m) :
    posetHeight S x ≤ m :=
  Finset.sup_le (fun C hC => by simp only [chainsEndingAt, mem_filter, mem_powerset] at hC; exact h_chain C hC.1 hC.2.2.2)
end DilworthTheorem
