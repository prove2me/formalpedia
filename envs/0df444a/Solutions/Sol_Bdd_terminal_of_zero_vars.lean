-- Prove2me | solution 1 for Bdd.terminal_of_zero_vars
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:10:42.557501+00:00
-- url     : https://prove2.me/submissions/a15888e2-f54f-4941-8c2a-5987a4e28b95

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
theorem _root_.solution {B : Bdd n m} : n = 0 → ∃ b, B.root = .terminal b := by
  intro h
  subst h
  cases hr : B.root with
  | terminal b => exact ⟨b, rfl⟩
  | node j => exact False.elim (Nat.not_lt_zero _ B.heap[j].var.2)
end Bdd
