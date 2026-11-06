-- Prove2me | solution 1 for CircuitLowerBound.Tab.holdsC_taut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:15:19.172329+00:00
-- url     : https://prove2.me/submissions/c736c210-883e-4608-8e22-d68de58591fd

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
namespace CircuitLowerBound.Tab
theorem _root_.solution (α : Atom N → ℕ → ℕ → Bool) (b Q P : ℕ) : HoldsC α b Q P taut := by
  intro t _ q _
  simp only [taut, holdsY]
  cases α .u (tval b t 0) (qval P q 0 + 0) <;> simp
end CircuitLowerBound.Tab
