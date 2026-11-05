-- Prove2me | solution 1 for CircuitLowerBound.Tab.stay_of_evals
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:31:33.647335+00:00
-- url     : https://prove2.me/submissions/903cf876-2a70-48b5-b81a-e8f91dd96c5f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Spec
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Frame
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
theorem _root_.solution {c₀ c : N.tm.Cfg} : ∀ n : ℕ, (flip bind N.tm.step)^[n] (some c₀) = some c → (stay N)^[n] c₀ = c := by
  intro n
  induction n generalizing c with
  | zero => intro h; simpa using h
  | succ n ih =>
    intro h
    rw [Function.iterate_succ_apply'] at h ⊢
    cases h' : (flip bind N.tm.step)^[n] (some c₀) with
    | none =>
      rw [h'] at h
      exact (Option.some_ne_none c (h.symm.trans rfl)).elim
    | some c' =>
      rw [h'] at h
      rw [ih h']
      have : N.tm.step c' = some c := h
      rw [stay, this]; rfl
end CircuitLowerBound.Tab
