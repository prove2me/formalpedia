-- Prove2me | solution 1 for DilworthTheorem.chain_inter_antichain_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:33:08.055842+00:00
-- url     : https://prove2.me/submissions/c329f650-7f2d-4c8c-b83e-8f83a31efadc

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
theorem _root_.solution (s t : Set α) (hs : IsChain s) (ht : IsAntichain t) :
    ∀ x y, x ∈ s ∩ t → y ∈ s ∩ t → x = y := by
  intro x y ⟨hxs, hxt⟩ ⟨hys, hyt⟩; by_contra hne
  rcases hs x y hxs hys with h | h <;> [exact (ht x y hxt hyt hne).1 h; exact (ht x y hxt hyt hne).2 h]
end DilworthTheorem
