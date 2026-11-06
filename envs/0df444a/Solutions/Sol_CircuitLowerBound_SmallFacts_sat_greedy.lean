-- Prove2me | solution 1 for CircuitLowerBound.SmallFacts.sat_greedy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:07:22.266521+00:00
-- url     : https://prove2.me/submissions/b4a407dd-10c8-46c2-8bfa-14ddc2a35f18

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Interfaces
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Small
import Theorems.Thm_CircuitLowerBound_SmallFacts_length_greedy
import Theorems.Thm_CircuitLowerBound_SmallFacts_sat_append
import Theorems.Thm_CircuitLowerBound_SmallFacts_sat_units
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
theorem _root_.solution {φ : Cnf} (h : Sat φ) (j : ℕ) : Sat (φ ++ units (greedy φ j)) := by
  classical
  induction j with
  | zero =>
    obtain ⟨a, ha⟩ := h
    exact ⟨a, sat_append.2 ⟨ha, by simp [greedy, units]⟩⟩
  | succ j ih =>
    rw [greedy]
    by_cases h0 : Sat (φ ++ units (greedy φ j ++ [false]))
    · simp [h0]
    · simp only [h0, decide_false, Bool.not_false]
      obtain ⟨a, ha⟩ := ih
      obtain ⟨h1, h2⟩ := sat_append.1 ha
      rw [sat_units] at h2
      have key : ∀ v : Bool, a j = v → ∀ C ∈ φ ++ units (greedy φ j ++ [v]), ∃ l ∈ C, a l.1 = l.2 := by
        intro v hv
        refine sat_append.2 ⟨h1, sat_units.2 fun i hi => ?_⟩
        rw [List.length_append, length_greedy, List.length_singleton] at hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · rw [List.getD_append _ _ _ _ (by rw [length_greedy]; exact hi)]
          exact h2 i (by rw [length_greedy]; exact hi)
        · rw [List.getD_append_right _ _ _ _ (by rw [length_greedy]), length_greedy]
          simpa using hv
      cases hv : a j with
      | false => exact absurd ⟨a, key false hv⟩ h0
      | true => exact ⟨a, key true hv⟩
end CircuitLowerBound.SmallFacts
