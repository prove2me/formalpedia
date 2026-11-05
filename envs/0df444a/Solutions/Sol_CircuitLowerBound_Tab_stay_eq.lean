-- Prove2me | solution 1 for CircuitLowerBound.Tab.stay_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:45:21.512876+00:00
-- url     : https://prove2.me/submissions/454f5e0f-84cb-4e46-8275-82fcfc56d250

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Spec
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Frame
import Theorems.Thm_CircuitLowerBound_Tab_stepAux_frame
import Theorems.Thm_CircuitLowerBound_Tab_pref_ofFn
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
theorem _root_.solution (c : N.tm.Cfg) : stay N c =
    ⟨(nxt N (caseOf N c)).l, (nxt N (caseOf N c)).var, fun k => (nxt N (caseOf N c)).stk k ++ (c.stk k).drop (dep N)⟩ := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none =>
    simp only [stay, FinTM2.step, TM2.step, nxt, caseOf, pref_ofFn, List.take_append_drop]
    rfl
  | some l =>
    have := stepAux_frame (N.tm.m l) v (fun k => (S k).take (dep N)) (fun k => (S k).drop (dep N)) fun k => by
      by_cases h : dep N ≤ (S k).length
      · left; rw [List.length_take, min_eq_left h]; exact ops_le_dep N l
      · right; exact List.drop_eq_nil_of_le (by omega)
    simp only [List.take_append_drop] at this
    simp only [stay, FinTM2.step, TM2.step, nxt, caseOf, pref_ofFn, this]
    rfl
end CircuitLowerBound.Tab
