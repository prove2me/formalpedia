-- Prove2me | solution 1 for CircuitLowerBound.Tab.Enc.step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:46:37.450276+00:00
-- url     : https://prove2.me/submissions/6a7e7b6f-992f-4b7d-b329-8a7e48a89f40

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Frame
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Sound
import Theorems.Thm_CircuitLowerBound_Tab_exists_case
import Theorems.Thm_CircuitLowerBound_Tab_length_nxt_le
import Theorems.Thm_CircuitLowerBound_Tab_stay_eq
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
namespace Enc
theorem _root_.solution (h : Spec N α b Q P) {t V : ℕ} {c : N.tm.Cfg} (ht : t < 2 ^ b) (hE : Enc N α t V c) (hd : dep N ≤ V) (hV : V ≤ 2 ^ Q) :
    Enc N α (t + 1) (V - dep N) (stay N c) := by
  obtain ⟨γ, hγ⟩ := exists_case h ht
  have e : γ = caseOf N c := by
    refine Prod.ext ((hE.lab _).1 (h.csLab t ht γ hγ)) (Prod.ext ((hE.var _).1 (h.csVar t ht γ hγ)) ?_)
    funext k j
    exact (hE.cell k _ j (lt_of_lt_of_le j.2 hd)).1 (h.csCell t ht γ k j hγ)
  subst e
  rw [stay_eq]
  refine ⟨fun x => h.nxLab t ht _ x hγ, fun x => h.nxVar t ht _ x hγ, fun k x q hq => ?_⟩
  change α (.cell k x) (t + 1) q = true ↔ x = ((nxt N (caseOf N c)).stk k ++ (c.stk k).drop (dep N))[q]?
  by_cases hqn : q < ((nxt N (caseOf N c)).stk k).length
  · rw [List.getElem?_append_left hqn]
    exact h.nxCell t ht _ k x q hqn hγ
  · have hqn : ((nxt N (caseOf N c)).stk k).length ≤ q := by omega
    have hn := length_nxt_le N (caseOf N c) k
    have hlen := (h.nxLen t ht _ k ⟨((nxt N (caseOf N c)).stk k).length, by omega⟩ hγ).2 rfl
    have hc := h.copy t ht (q - ((nxt N (caseOf N c)).stk k).length) (by omega) k _ x hlen
    simp only [Nat.sub_add_cancel hqn] at hc
    rw [hc, hE.cell k x _ (by omega), List.getElem?_append_right hqn, List.getElem?_drop, Nat.add_comm]
end Enc
end CircuitLowerBound.Tab
