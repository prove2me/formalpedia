-- Prove2me | solution 1 for CircuitLowerBound.Tab.exists_init
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:43:31.316208+00:00
-- url     : https://prove2.me/submissions/6130899f-66ee-4fd9-9960-dcd1580b96ad

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Frame
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Sound
import Theorems.Thm_CircuitLowerBound_Tab_initList_stk_self
import Theorems.Thm_CircuitLowerBound_Tab_initList_stk_of_ne
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_P2M_CircuitLowerBound_Tab_getElem__pref_6e5abd1d4764
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Tab
open ENP Turing
variable (N : TM2ComputableAux Bool Bool)
variable {N} [Finite (Case N)] {α : Atom N → ℕ → ℕ → Bool} {b Q P : ℕ}
namespace CircuitLowerBound.Tab
theorem _root_.solution (h : Spec N α b Q P) (hP : P + 1 < 2 ^ Q) :
    ∃ y : List Bool, Enc N α 0 (2 ^ Q) (initList N.tm ((unary P ++ y).map N.inputAlphabet.invFun)) := by
  classical
  obtain ⟨f, hfdef⟩ : ∃ f : ℕ → Option (N.tm.Γ N.tm.k₀), ∀ q, f q = if α (.cell N.tm.k₀ none) 0 q = true then none
      else if α (.cell N.tm.k₀ (some (N.inputAlphabet.symm false))) 0 q = true then some (N.inputAlphabet.symm false) else some (N.inputAlphabet.symm true) := ⟨_, fun _ => rfl⟩
  have hf : ∀ q < 2 ^ Q, ∀ x, α (.cell N.tm.k₀ x) 0 q = true ↔ x = f q := by
    intro q hq x
    have hone : α (.cell N.tm.k₀ (f q)) 0 q = true := by
      rw [hfdef]
      split_ifs with h1 h2
      · exact h1
      · exact h2
      · rcases h.iSome q hq with h3 | h3 | h3
        · exact absurd h3 h1
        · exact absurd h3 h2
        · exact h3
    constructor
    · intro hx
      by_contra hne
      rcases h.iMost q hq x (f q) hne with h4 | h4
      · rw [hx] at h4; cases h4
      · rw [hone] at h4; cases h4
    · rintro rfl
      exact hone
  obtain ⟨S, hSdef⟩ : ∃ S, S = pref ((List.range (2 ^ Q)).map f) := ⟨_, rfl⟩
  have hL : ∀ i, ((List.range (2 ^ Q)).map f)[i]? = if i < 2 ^ Q then some (f i) else none := by
    intro i
    by_cases hi : i < 2 ^ Q <;> simp [hi]
  have hS : ∀ q < 2 ^ Q, S[q]? = f q := by
    intro q hq
    rw [hSdef, getElem?_pref _ ?_ q (by simpa using hq), hL, if_pos hq]
    · rfl
    · intro i hi x hx
      rw [hL] at hi hx
      split_ifs at hi hx with hi1 hx1
      have hi2 : f i = none := Option.some.inj hi
      have hx2 : f (i + 1) = x := Option.some.inj hx
      have := h.iBlank i hi1 ((hf i hi1 none).2 hi2.symm)
      rw [← hx2]
      exact ((hf (i + 1) hx1 none).1 this).symm
  have hu : ∀ i, i ≤ P → α .u 0 (P - i) = true := by
    intro i
    induction i with
    | zero => intro _; exact h.uP
    | succ i ih =>
      intro hi
      have := h.uStep (P - (i + 1)) (by omega)
      rw [show P - (i + 1) + 1 = P - i by omega] at this
      exact this (ih (by omega))
  have h1 : ∀ q < P, f q = some (N.inputAlphabet.symm true) := by
    intro q hq
    have := hu (P - (q + 1)) (by omega)
    rw [show P - (P - (q + 1)) = q + 1 by omega] at this
    exact ((hf q (by omega) _).1 (h.uOne q (by omega) this)).symm
  have h0 : f P = some (N.inputAlphabet.symm false) := ((hf P (by omega) _).1 h.cellP).symm
  have htake : S.take (P + 1) = (unary P).map N.inputAlphabet.invFun := by
    apply List.ext_getElem?
    intro q
    by_cases hq : q < P + 1
    · rw [List.getElem?_take_of_lt hq, hS q (by omega)]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hq with hq' | rfl
      · rw [h1 q hq']
        simp [unary, List.getElem?_append_left, hq']
      · rw [h0]
        simp [unary]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp [unary]; omega)]
  refine ⟨(S.drop (P + 1)).map N.inputAlphabet, ?_⟩
  have hS' : (unary P ++ (S.drop (P + 1)).map N.inputAlphabet).map N.inputAlphabet.invFun = S := by
    rw [List.map_append, ← htake, List.map_map]
    have : (N.inputAlphabet.invFun ∘ N.inputAlphabet) = id := by funext z; simp
    rw [this, List.map_id, List.take_append_drop]
  rw [hS']
  refine ⟨h.iLab, h.iVar, fun k x q hq => ?_⟩
  by_cases hk : k = N.tm.k₀
  · subst hk
    rw [initList_stk_self, hS q hq]
    exact hf q hq x
  · rw [initList_stk_of_ne N _ hk]
    simpa using h.iCell q hq k hk x
end CircuitLowerBound.Tab
