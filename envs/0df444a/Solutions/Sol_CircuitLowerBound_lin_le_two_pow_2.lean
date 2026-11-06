-- Prove2me | solution 2 for CircuitLowerBound.lin_le_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:05:27.49258+00:00
-- url     : https://prove2.me/submissions/19474dcc-114c-4dcc-a86f-023fd665b219

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Interfaces
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Main

set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork Turing
namespace CircuitLowerBound
theorem _root_.solution : ∀ x : ℕ, 8 ≤ x → 24 * x + 26 ≤ 2 ^ x := by
  intro x hx
  induction x, hx using Nat.le_induction with
  | base => norm_num
  | succ x hx ih => rw [pow_succ]; omega
end CircuitLowerBound
