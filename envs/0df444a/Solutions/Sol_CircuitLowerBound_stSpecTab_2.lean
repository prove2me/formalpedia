-- Prove2me | solution 2 for CircuitLowerBound.stSpecTab
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:37:47.209995+00:00
-- url     : https://prove2.me/submissions/c01cf94c-a53e-4d33-a178-4c532f40bc07

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Frame
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Table
import Theorems.Thm_CircuitLowerBound_Tab_spec_of_table
import Theorems.Thm_CircuitLowerBound_Tab_table_of_spec
import Theorems.Thm_CircuitLowerBound_Tab_table_dq
import Theorems.Thm_CircuitLowerBound_Tab_num_injective
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open CircuitLowerBound
open Tab Turing
namespace CircuitLowerBound
theorem _root_.solution : StSpecTab := by
  intro N _ hfin
  have : ∀ k, Finite (N.tm.Γ k) := hfin
  refine ⟨codeTab N, ?_, rfl, fun b Q P => ?_⟩
  · intro c hc l hl
    obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
    have hdq := table_dq c' hc'
    have hlam : 2 * dep N + 2 < 2 ^ lamOf N := Nat.lt_size_self _
    have hnum : ∀ a : Atom N, 1 ≤ num a ∧ num a < 2 ^ kb (codeTab N) := fun a =>
      ⟨by simp [num], lt_trans (by have := (Finite.equivFin (Atom N) a).isLt; simp only [num]; omega) (Nat.lt_size_self _)⟩
    have hl' : lam (codeTab N) = lamOf N := rfl
    simp only [lits, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · exact ⟨(hnum _).1, (hnum _).2, by rw [hl']; simp only [nl]; omega⟩
    · exact ⟨(hnum _).1, (hnum _).2, by rw [hl']; simp only [nl]; omega⟩
    · exact ⟨(hnum _).1, (hnum _).2, by rw [hl']; simp only [nl]; omega⟩
  · have key : ∀ (β : ℕ → ℕ → ℕ → Bool) (α : Atom N → ℕ → ℕ → Bool), (∀ a t q, β (num a) t q = α a t q) →
        ((∀ c ∈ tab (codeTab N), ∀ t < 2 ^ b, ∀ q < 2 ^ Q, ∃ l ∈ lits c, holdsT β b P t q l) ↔ ∀ c ∈ table N, HoldsC α b Q P c) := by
      intro β α h
      simp only [tab, codeTab, List.forall_mem_map, lits, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, holdsT, nl, h]
      rfl
    constructor
    · rintro ⟨β, hβ⟩
      exact ⟨fun a t q => β (num a) t q, spec_of_table ((key β _ fun _ _ _ => rfl).1 hβ)⟩
    · rintro ⟨α, hα⟩
      classical
      refine ⟨fun k t q => if h : ∃ a, num a = k then α h.choose t q else false, (key _ α fun a t q => ?_).2 (table_of_spec hα)⟩
      have h : ∃ a', num a' = num a := ⟨a, rfl⟩
      rw [dif_pos h, num_injective h.choose_spec]
end CircuitLowerBound
