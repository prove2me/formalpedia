-- Prove2me | solution 1 for CircuitLowerBound.Tab.initList_stk_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:28:27.798204+00:00
-- url     : https://prove2.me/submissions/7d97e980-a3e2-43c1-8ba2-f58691f53df5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Frame
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Sound
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
namespace CircuitLowerBound.Tab
theorem _root_.solution (s : List (N.tm.Γ N.tm.k₀)) : (initList N.tm s).stk N.tm.k₀ = s := by simp [initList]
end CircuitLowerBound.Tab
