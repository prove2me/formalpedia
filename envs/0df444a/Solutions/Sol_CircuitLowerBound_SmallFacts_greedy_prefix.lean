-- Prove2me | solution 1 for CircuitLowerBound.SmallFacts.greedy_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:07:21.26811+00:00
-- url     : https://prove2.me/submissions/085b6dfe-97d8-4c20-95ac-e9a5d1cdc8c8

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
theorem _root_.solution (φ : Cnf) {j j' : ℕ} (h : j ≤ j') : greedy φ j <+: greedy φ j' := by
  induction j', h using Nat.le_induction with
  | base => exact List.prefix_rfl
  | succ j' _ ih => exact ih.trans (by rw [greedy]; exact List.prefix_append _ _)
end CircuitLowerBound.SmallFacts
