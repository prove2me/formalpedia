-- Prove2me | solution 1 for CircuitLowerBound.Tab.bool_dec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:41:37.459106+00:00
-- url     : https://prove2.me/submissions/92d2d8e0-db42-427c-a4ce-fe34df19da9c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Frame
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Table
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Tab
open ENP Turing
variable (N : TM2ComputableAux Bool Bool)
variable {N}
variable (N) [Finite (Case N)] [∀ k, Finite (N.tm.Γ k)]
variable {N}
namespace CircuitLowerBound.Tab
theorem _root_.solution {y : Bool} {p : Prop} [Decidable p] : y = decide p ↔ (y = true ↔ p) := by
  by_cases hp : p <;> cases y <;> simp [hp]
end CircuitLowerBound.Tab
