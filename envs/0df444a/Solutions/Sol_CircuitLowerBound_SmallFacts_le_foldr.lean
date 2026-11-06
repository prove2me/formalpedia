-- Prove2me | solution 1 for CircuitLowerBound.SmallFacts.le_foldr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:13:57.761177+00:00
-- url     : https://prove2.me/submissions/91bb8564-780d-4b4c-8ac1-5d0941f5b153

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Interfaces
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Small

set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.SmallFacts
namespace CircuitLowerBound.SmallFacts
theorem _root_.solution (j : ℕ) (w : List Bool) : j ≤ (List.replicate j true ++ w).foldr Nat.bit 0 := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ j ih =>
    rw [List.replicate_succ, List.cons_append, List.foldr_cons, Nat.bit_true_apply]
    omega
end CircuitLowerBound.SmallFacts
