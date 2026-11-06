-- Prove2me | solution 1 for ExplicitCost.pricesScale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:11:09.676204+00:00
-- url     : https://prove2.me/submissions/7d5cf56b-4af1-4e3a-be0e-2913911d0ddb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_AnswersDefs
import Definitions.Def_QueryMachines_Runs
import Definitions.Def_QueryMachines_Poly
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Answers
import Theorems.Thm_ExplicitCost_sum_map_le_mul

set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines Printed
variable {Q A A' α β : Type}
namespace ExplicitCost
theorem _root_.solution : PricesScale := fun _ _ _ _ _ _ w w' _ T _ k _ hk h ⟨own, L, hr, hle⟩ => ⟨own, L, hr, by
  have h1 := sum_map_le_mul h L
  have h2 := Nat.mul_le_mul_left k hle
  have h3 : own ≤ k * own := Nat.le_mul_of_pos_left _ hk
  rw [Nat.mul_add] at h2
  omega⟩
end ExplicitCost
