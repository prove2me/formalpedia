-- Prove2me | solution 1 for CircuitLowerBound.Tab.eq_haltList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:42:55.486049+00:00
-- url     : https://prove2.me/submissions/230b9c46-6f8a-4393-8a13-ebe7f7b8724a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Frame
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Sound
import Theorems.Thm_CircuitLowerBound_Tab_haltList_stk_self
import Theorems.Thm_CircuitLowerBound_Tab_haltList_stk_of_ne
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
variable {N} [Finite (Case N)] {α : Atom N → ℕ → ℕ → Bool} {b Q P : ℕ}
namespace CircuitLowerBound.Tab
theorem _root_.solution (h : Spec N α b Q P) {V : ℕ} {c : N.tm.Cfg} (hE : Enc N α (2 ^ b) V c) (hV : 2 ≤ V) :
    c = haltList N.tm [N.outputAlphabet.invFun true] := by
  obtain ⟨l, v, S⟩ := c
  have hl : none = l := (hE.lab none).1 h.fLab
  have hv : N.tm.initialState = v := (hE.var _).1 h.fVar
  have hS : S = (haltList N.tm [N.outputAlphabet.invFun true]).stk := by
    funext k
    by_cases hk : k = N.tm.k₁
    · subst hk
      rw [haltList_stk_self]
      have a0 : some (N.outputAlphabet.symm true) = (S N.tm.k₁)[0]? := (hE.cell _ _ 0 (by omega)).1 h.fOut0
      have a1 : none = (S N.tm.k₁)[1]? := (hE.cell _ _ 1 (by omega)).1 h.fOut1
      cases hS : S N.tm.k₁ with
      | nil => simp [hS] at a0
      | cons z r =>
        cases r with
        | nil => simp [hS] at a0; rw [← a0]; rfl
        | cons z' r => simp [hS] at a1
    · rw [haltList_stk_of_ne N _ hk]
      have a0 : none = (S k)[0]? := (hE.cell _ _ 0 (by omega)).1 (h.fOther k hk)
      cases hS : S k with
      | nil => rfl
      | cons z r => simp [hS] at a0
  subst hl hv hS
  rfl
end CircuitLowerBound.Tab
