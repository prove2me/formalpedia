-- Prove2me | solution 1 for DilworthTheorem.antichain_subset_upperCone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:32:08.249165+00:00
-- url     : https://prove2.me/submissions/9eef604a-dc6b-4580-bebf-7e0d51a8e338

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
theorem _root_.solution {S A : Finset α} (hAS : A ⊆ S) : A ⊆ upperCone S A :=
  fun x hx => mem_filter.mpr ⟨hAS hx, x, hx, le_rfl⟩
end DilworthTheorem
