-- Prove2me | solution 1 for DilworthTheorem.isChain_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:29:40.128085+00:00
-- url     : https://prove2.me/submissions/61629ab9-7437-4161-aac2-5bf6b0237cb7

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
theorem _root_.solution (x : α) : IsChain ({x} : Set α) := by
  rintro y z rfl rfl; exact Or.inl le_rfl
end DilworthTheorem
