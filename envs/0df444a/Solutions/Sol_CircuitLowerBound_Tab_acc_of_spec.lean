-- Prove2me | solution 1 for CircuitLowerBound.Tab.acc_of_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:47:37.39146+00:00
-- url     : https://prove2.me/submissions/58aae0b0-bf28-4985-baa7-c7b81fdf5668

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Frame
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Sound
import Theorems.Thm_CircuitLowerBound_Tab_Enc_step
import Theorems.Thm_CircuitLowerBound_Tab_exists_init
import Theorems.Thm_CircuitLowerBound_Tab_eq_haltList
import Theorems.Thm_CircuitLowerBound_Tab_evals_of_stay
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
theorem _root_.solution (hP : P + 2 ≤ 2 ^ b) (h : Spec N α b (b + lamOf N) P) : Acc N P (2 ^ b) := by
  have hlam : 2 * dep N + 2 < 2 ^ lamOf N := Nat.lt_size_self _
  have hQ : 2 ^ (b + lamOf N) = 2 ^ b * 2 ^ lamOf N := pow_add _ _ _
  have hb : 0 < 2 ^ b := by positivity
  have hbig : 2 ^ b * dep N + 2 ^ b * 2 ≤ 2 ^ (b + lamOf N) := by
    rw [hQ, ← Nat.mul_add]
    exact Nat.mul_le_mul_left _ (by omega)
  obtain ⟨y, h0⟩ := exists_init h (by omega)
  have hrun : ∀ t, t ≤ 2 ^ b → Enc N α t (2 ^ (b + lamOf N) - t * dep N) ((stay N)^[t] (initList N.tm ((unary P ++ y).map N.inputAlphabet.invFun))) := by
    intro t
    induction t with
    | zero => intro _; simpa using h0
    | succ t ih =>
      intro ht
      have hle : (t + 1) * dep N ≤ 2 ^ b * dep N := Nat.mul_le_mul_right _ ht
      rw [Function.iterate_succ_apply', Nat.add_mul, Nat.one_mul, ← Nat.sub_sub]
      rw [Nat.add_mul, Nat.one_mul] at hle
      exact (ih (by omega)).step h (by omega) (by omega) (Nat.sub_le _ _)
  have hfin := eq_haltList h (hrun _ le_rfl) (by omega)
  obtain ⟨n, hn, hr⟩ := evals_of_stay N _ _ hfin
  exact ⟨y, ⟨⟨⟨n, hr⟩, hn⟩⟩⟩
end CircuitLowerBound.Tab
