-- Prove2me | solution 1 for DilworthTheorem.isChain_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:41:42.461085+00:00
-- url     : https://prove2.me/submissions/6d704838-74a7-4ea9-b2fb-90c55800be45

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
theorem _root_.solution {s t : Set α} (hst : s ⊆ t) (ht : IsChain t) : IsChain s :=
  fun x y hx hy => ht x y (hst hx) (hst hy)
end DilworthTheorem
