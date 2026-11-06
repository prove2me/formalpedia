-- Prove2me | solution 1 for ExplicitCost.K_le_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:12:30.778721+00:00
-- url     : https://prove2.me/submissions/759985e9-f102-46ec-bde8-c21ded0f8d8c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_AnswersDefs
import Definitions.Def_ToTuring_Poly_Range
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_ToTuring_Lib_Unary
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Numbers
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution (x₀ l : ℕ) : Levels.Gen.K x₀ l ≤ Levels.Gen.K x₀ (l + 1) := by
  have h1 : 1 ≤ 2 ^ (3 * l + x₀) := Nat.one_le_two_pow
  have h2 : Levels.Gen.K x₀ l ≤ 2 ^ (3 * l + x₀) * Levels.Gen.K x₀ l := Nat.le_mul_of_pos_left _ h1
  exact h2.trans (Nat.le_self_pow (by norm_num) _)
end ExplicitCost
