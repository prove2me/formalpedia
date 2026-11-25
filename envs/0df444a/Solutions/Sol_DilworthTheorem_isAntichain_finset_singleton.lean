-- Prove2me | solution 1 for DilworthTheorem.isAntichain_finset_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:33:47.405204+00:00
-- url     : https://prove2.me/submissions/dd59e427-a358-4a63-9286-3c4ddbf6a997

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
import Theorems.Thm_DilworthTheorem_isAntichain_singleton

set_option autoImplicit true
open DilworthTheorem
open Finset
open Classical
variable {α : Type*} [PartialOrder α]
namespace DilworthTheorem
theorem _root_.solution (x : α) : IsAntichain (({x} : Finset α) : Set α) := by
  rw [coe_singleton]; exact isAntichain_singleton x
end DilworthTheorem
