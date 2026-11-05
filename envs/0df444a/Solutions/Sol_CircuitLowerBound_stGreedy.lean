-- Prove2me | solution 1 for CircuitLowerBound.stGreedy
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:21:43.073084+00:00
-- url     : https://prove2.me/submissions/1aa39eb2-b582-489b-b2dc-d80ebddfa893

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Interfaces
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Small
set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open SmallFacts

namespace CircuitLowerBound.SmallFacts

theorem length_greedy (φ : Cnf) (j : ℕ) : (greedy φ j).length = j := by
  induction j with
  | zero => rfl
  | succ j ih => simp [greedy, ih]

theorem greedy_prefix (φ : Cnf) {j j' : ℕ} (h : j ≤ j') : greedy φ j <+: greedy φ j' := by
  induction j', h using Nat.le_induction with
  | base => exact List.prefix_rfl
  | succ j' _ ih => exact ih.trans (by rw [greedy]; exact List.prefix_append _ _)

theorem sat_append {φ ψ : Cnf} {a : ℕ → Bool} : (∀ C ∈ φ ++ ψ, ∃ l ∈ C, a l.1 = l.2) ↔ (∀ C ∈ φ, ∃ l ∈ C, a l.1 = l.2) ∧ ∀ C ∈ ψ, ∃ l ∈ C, a l.1 = l.2 :=
  List.forall_mem_append

theorem sat_units {w : List Bool} {a : ℕ → Bool} : (∀ C ∈ units w, ∃ l ∈ C, a l.1 = l.2) ↔ ∀ i < w.length, a i = w.getD i false := by
  simp [units]

/-- The values found so far can always be continued to a satisfying assignment. -/
theorem sat_greedy {φ : Cnf} (h : Sat φ) (j : ℕ) : Sat (φ ++ units (greedy φ j)) := by
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

theorem solution : StGreedy := by
  intro φ M hM hs C hC
  obtain ⟨a, ha⟩ := sat_greedy hs M
  obtain ⟨h1, h2⟩ := sat_append.1 ha
  rw [sat_units, length_greedy] at h2
  obtain ⟨l, hl, hal⟩ := h1 C hC
  refine ⟨l, hl, ?_⟩
  have hlt := hM C hC l hl
  obtain ⟨r, hr⟩ := greedy_prefix φ (show l.1 + 1 ≤ M from hlt)
  rw [← hal, h2 l.1 hlt, ← hr, List.getD_append _ _ _ _ (by rw [length_greedy]; omega)]
