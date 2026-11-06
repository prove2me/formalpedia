-- Prove2me | solution 1 for CircuitLowerBound.SmallFacts.length_flat15
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:14:18.764001+00:00
-- url     : https://prove2.me/submissions/bc67aee4-075a-4465-8868-3fb5d0b196ad

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Interfaces
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Small
import Theorems.Thm_CircuitLowerBound_SmallFacts_length_n15

set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.SmallFacts
namespace CircuitLowerBound.SmallFacts
theorem _root_.solution (X : List TCl) : ((X.map n15).flatten).length = 15 * X.length := by
  induction X with
  | nil => rfl
  | cons c X ih => rw [List.map_cons, List.flatten_cons, List.length_append, ih, length_n15, List.length_cons]; ring
end CircuitLowerBound.SmallFacts
