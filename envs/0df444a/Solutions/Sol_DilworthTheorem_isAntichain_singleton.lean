-- Prove2me | solution 1 for DilworthTheorem.isAntichain_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:30:04.460811+00:00
-- url     : https://prove2.me/submissions/2b672fba-b45c-42e7-9f86-91425d7fba51

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
theorem _root_.solution (x : α) : IsAntichain ({x} : Set α) := by
  rintro y z rfl rfl hne; exact (hne rfl).elim
end DilworthTheorem
