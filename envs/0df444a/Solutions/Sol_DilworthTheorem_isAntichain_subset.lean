-- Prove2me | solution 1 for DilworthTheorem.isAntichain_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:28:27.699793+00:00
-- url     : https://prove2.me/submissions/d033db72-de4c-4638-b802-0be8ead2b5dd

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
theorem _root_.solution {s t : Set α} (hst : s ⊆ t) (ht : IsAntichain t) : IsAntichain s :=
  fun x y hx hy => ht x y (hst hx) (hst hy)
end DilworthTheorem
