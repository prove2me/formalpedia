-- Prove2me | solution 1 for CircuitLowerBound.Tab.length_nxt_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:43:26.432557+00:00
-- url     : https://prove2.me/submissions/40d2bf95-9704-4d2d-bb5d-8532f98dbe2e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Spec
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Frame
import Theorems.Thm_CircuitLowerBound_Tab_length_stepAux_le
import Theorems.Thm_CircuitLowerBound_Tab_length_pref_le
import Theorems.Thm_CircuitLowerBound_Tab_ops_le_dep
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
theorem _root_.solution (γ : Case N) (k : N.tm.K) : ((nxt N γ).stk k).length ≤ 2 * dep N := by
  obtain ⟨l, v, w⟩ := γ
  have h1 : (pref (List.ofFn (w k))).length ≤ dep N := (length_pref_le _).trans (by simp)
  cases l with
  | none => simp only [nxt]; omega
  | some l =>
    simp only [nxt]
    have := length_stepAux_le (N.tm.m l) v (fun k => pref (List.ofFn (w k))) k
    have := ops_le_dep N l
    omega
end CircuitLowerBound.Tab
