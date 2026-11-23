-- Prove2me | solution 1 for Bdd.terminal_of_zero_heap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:10:45.960107+00:00
-- url     : https://prove2.me/submissions/faaa295f-56df-4705-8c8c-af2a82bab255

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic

set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
namespace Bdd
theorem _root_.solution {B : Bdd n m} : m = 0 → ∃ b, B.root = .terminal b := by
  intro h
  subst h
  cases hr : B.root with
  | terminal b => exact ⟨b, rfl⟩
  | node j => exact False.elim (Nat.not_lt_zero _ j.2)
end Bdd
