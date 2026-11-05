-- Prove2me | solution 1 for ExplicitCost.K_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:50:42.054379+00:00
-- url     : https://prove2.me/submissions/3c5d83b4-c3bb-40f2-aa7b-7f9290280895

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_AnswersDefs
import Definitions.Def_ToTuring_Poly_Range
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_ToTuring_Lib_Unary
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Numbers

set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution (x₀ l : ℕ) : 1 ≤ Levels.Gen.K x₀ l := by
  induction l with
  | zero => exact Nat.one_le_two_pow
  | succ l ih => exact Nat.pow_pos (Nat.mul_pos (Nat.pow_pos (by norm_num)) ih)
end ExplicitCost
