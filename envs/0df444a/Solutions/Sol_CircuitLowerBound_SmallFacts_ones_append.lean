-- Prove2me | solution 1 for CircuitLowerBound.SmallFacts.ones_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:11:12.341583+00:00
-- url     : https://prove2.me/submissions/93e013d6-b259-4b7b-9d64-6aae413c7d1d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Interfaces
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Small
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.SmallFacts
namespace CircuitLowerBound.SmallFacts
theorem _root_.solution (j : ℕ) (x : List Bool) : ones (List.replicate j true ++ false :: x) = j := by
  induction j with
  | zero => simp [ones]
  | succ j ih =>
    simp only [ones, List.replicate_succ, List.cons_append, List.takeWhile_cons, id, if_true, List.length_cons] at ih ⊢
    rw [ih]
end CircuitLowerBound.SmallFacts
