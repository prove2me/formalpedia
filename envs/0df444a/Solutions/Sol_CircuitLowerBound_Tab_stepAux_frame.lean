-- Prove2me | solution 1 for CircuitLowerBound.Tab.stepAux_frame
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:43:09.297426+00:00
-- url     : https://prove2.me/submissions/034d01d3-0694-4b78-83f4-73eeb96f3eb7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Spec
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Frame
import Theorems.Thm_CircuitLowerBound_Tab_update_append
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Tab
open ENP Turing
variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
namespace CircuitLowerBound.Tab
theorem _root_.solution (q : TM2.Stmt Γ Λ σ) : ∀ (v : σ) (A R : ∀ k, List (Γ k)), (∀ k, ops q ≤ (A k).length ∨ R k = []) →
    TM2.stepAux q v (fun k => A k ++ R k) =
      ⟨(TM2.stepAux q v A).l, (TM2.stepAux q v A).var, fun k => (TM2.stepAux q v A).stk k ++ R k⟩ := by
  induction q with
  | push k f q ih =>
    intro v A R h
    simp only [TM2.stepAux]
    rw [← List.cons_append, update_append, ih]
    intro k'
    rcases h k' with h | h
    · left
      by_cases e : k' = k
      · subst e; simp [ops] at h ⊢; omega
      · simp [Function.update_of_ne e, ops] at h ⊢; omega
    · exact Or.inr h
  | peek k f q ih =>
    intro v A R h
    have hh : (A k ++ R k).head? = (A k).head? := by
      rcases h k with h | h
      · cases hA : A k with
        | nil => simp [hA, ops] at h
        | cons a l => simp
      · simp [h]
    simp only [TM2.stepAux, hh]
    exact ih _ A R fun k' => (h k').imp (fun h => by simp [ops] at h; omega) id
  | pop k f q ih =>
    intro v A R h
    have hh : (A k ++ R k).head? = (A k).head? ∧ (A k ++ R k).tail = (A k).tail ++ R k := by
      rcases h k with h | h
      · cases hA : A k with
        | nil => simp [hA, ops] at h
        | cons a l => simp
      · simp [h]
    simp only [TM2.stepAux, hh.1, hh.2]
    rw [update_append, ih]
    intro k'
    rcases h k' with h | h
    · left
      by_cases e : k' = k
      · subst e; simp [ops] at h ⊢; omega
      · simp [Function.update_of_ne e, ops] at h ⊢; omega
    · exact Or.inr h
  | load a q ih =>
    intro v A R h
    simp only [TM2.stepAux]
    exact ih _ A R h
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro v A R h
    simp only [TM2.stepAux]
    cases f v
    · exact ih₂ v A R fun k => (h k).imp (fun h => le_trans (le_max_right _ _) h) id
    · exact ih₁ v A R fun k => (h k).imp (fun h => le_trans (le_max_left _ _) h) id
  | goto f => intro v A R _; rfl
  | halt => intro v A R _; rfl
end CircuitLowerBound.Tab
