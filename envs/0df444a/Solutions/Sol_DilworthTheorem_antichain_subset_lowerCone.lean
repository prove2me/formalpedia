-- Prove2me | solution 1 for DilworthTheorem.antichain_subset_lowerCone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:31:59.774558+00:00
-- url     : https://prove2.me/submissions/82a2fd9e-f40f-4f52-967a-1f8b2542399e

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
theorem _root_.solution {S A : Finset α} (hAS : A ⊆ S) : A ⊆ lowerCone S A :=
  fun x hx => mem_filter.mpr ⟨hAS hx, x, hx, le_rfl⟩
end DilworthTheorem
