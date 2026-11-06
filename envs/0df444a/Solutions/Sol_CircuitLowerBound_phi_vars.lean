-- Prove2me | solution 1 for CircuitLowerBound.phi_vars
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:05:16.240136+00:00
-- url     : https://prove2.me/submissions/df06e68d-8dfa-4fee-983c-e7bdee8be230

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Interfaces
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Main
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork Turing
namespace CircuitLowerBound
theorem _root_.solution (hV : StVars) (m : ℕ) : ∀ D ∈ Phi m, ∀ l ∈ D, l.1 < 2 ^ m := by
  intro D hD l hl
  unfold Phi at hD
  split_ifs at hD with h1 h2 h3 h4
  · exact hV _ _ _ h2 D hD l hl
  · simp at hD
  · simp only [List.mem_singleton] at hD; subst hD; simp at hl
  · simp at hD
  · simp at hD
end CircuitLowerBound
