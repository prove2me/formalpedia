-- Prove2me | solution 1 for CircuitLowerBound.Tab.evals_of_stay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:42:42.810616+00:00
-- url     : https://prove2.me/submissions/50370cca-2085-4f02-87f6-f07ad0848aaf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Spec
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Frame
import Theorems.Thm_CircuitLowerBound_Tab_iterate_stay_of_halted
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
theorem _root_.solution {h : N.tm.Cfg} : ∀ (T : ℕ) (c₀ : N.tm.Cfg), (stay N)^[T] c₀ = h →
    ∃ n ≤ T, (flip bind N.tm.step)^[n] (some c₀) = some h := by
  intro T
  induction T with
  | zero => intro c₀ e; exact ⟨0, le_rfl, by simpa using e⟩
  | succ T ih =>
    intro c₀ e
    by_cases h0 : c₀.l = none
    · rw [iterate_stay_of_halted N h0] at e
      exact ⟨0, Nat.zero_le _, by simpa using e⟩
    · rw [Function.iterate_succ_apply] at e
      obtain ⟨n, hn, hr⟩ := ih _ e
      refine ⟨n + 1, by omega, ?_⟩
      rw [Function.iterate_succ_apply]
      have : flip bind N.tm.step (some c₀) = some (stay N c₀) := by
        obtain ⟨l, v, S⟩ := c₀
        cases l with
        | none => exact absurd rfl h0
        | some l => rfl
      rw [this, hr]
end CircuitLowerBound.Tab
