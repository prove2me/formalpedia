-- Prove2me | solution 1 for CircuitLowerBound.Alg.exists_guess
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:19:18.697382+00:00
-- url     : https://prove2.me/submissions/d4943be8-c21d-42ab-8499-ced3a1aace34

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Alg_Parse
import Definitions.Def_GraphProblems_Engine
import Definitions.Def_PaddedDescent_Host
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Alg_Machine
import Theorems.Thm_CircuitLowerBound_Alg_pre_cases
import Theorems.Thm_CircuitLowerBound_Alg_not_sat_false
import Theorems.Thm_CircuitLowerBound_Parse_decC_encC
import Theorems.Thm_CircuitLowerBound_Parse_length_encC
import Theorems.Thm_CircuitLowerBound_Parse_ones_unary_append
import Theorems.Thm_CircuitLowerBound_Parse_rest_unary_append
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_length_toWord
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local simp] Groundwork.length_toWord



set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork Turing Parse
open CircuitLowerBound.Alg
variable {F : (MCode × List Unit × ℕ) × List GateD → List Unit × Cnf} {fb : List Unit → Bool}
variable {a₀ : ℕ} {g : MCode → ℕ}
namespace CircuitLowerBound.Alg
theorem _root_.solution (hF : FormOK a₀ g F) (hb : FlipOK fb) (hN : StNorm) {m : ℕ} (hm : 1 ≤ m) (hpos : pos m ≤ top (nu m)) (C : Circuit)
    (hC : ∀ D ∈ Phi m, ∃ l ∈ D, eval C (toWord m l.1) = l.2) :
    ∃ y : List Bool, y.length = (m + C.length) + 1 + C.length * (4 + 2 * (m + C.length)) ∧ ¬Sat (pre F fb (unary m ++ y)).2 ∧
      (pre F fb (unary m ++ y)).1.length ≤ 3 * C.length + a₀ * (m + 1) + g (codeOf (nu m)) := by
  obtain ⟨C', hW, hl, hev⟩ := hN m C hm
  have hdec : decC (encC (m + C.length) C') = C' := by
    refine decC_encC fun G hG => ?_
    obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 hG
    have h1 := hW t ht
    have h2 : m + t < 2 ^ (m + C.length) := lt_of_lt_of_le (by omega) (Nat.lt_two_pow_self (n := m + C.length)).le
    exact ⟨h1.1.trans h2, h1.2.trans h2⟩
  refine ⟨encC (m + C.length) C', by rw [length_encC, hl], ?_⟩
  have ho := Parse.ones_unary_append m (encC (m + C.length) C')
  have hr := Parse.rest_unary_append m (encC (m + C.length) C')
  rcases pre_cases F fb (unary m ++ encC (m + C.length) C') with ⟨h1, h2, h3, e⟩ | ⟨_, _, h3, _⟩ | ⟨_, _, e⟩ | ⟨h1, h2, _⟩ | ⟨_, _, e⟩ | ⟨h1, _⟩
  · rw [ho] at h1 h2
    rw [ho, hr, hdec] at e h3
    rw [e]
    obtain ⟨-, h4, h5⟩ := hF _ _ _ _ h2 h3
    refine ⟨?_, by rw [← hl]; exact h4⟩
    rw [h5, not_not]
    intro D hD
    have h6 : Phi m = tabF (codeOf (nu m)) m (next m) := by
      unfold Phi
      rw [if_pos h1, if_pos h2]
    obtain ⟨l, hl', h7⟩ := hC D (h6 ▸ hD)
    exact ⟨l, hl', by rw [hev _ (length_toWord _ _)]; exact h7⟩
  · rw [ho, hr, hdec] at h3
    exact absurd hW h3
  · rw [e]
    exact ⟨not_sat_false, Nat.zero_le _⟩
  · rw [ho] at h1 h2
    have h6 : Phi m = [[]] := by
      unfold Phi
      rw [if_neg (by omega), if_pos h1, if_pos ((hb _ h1).1 h2)]
    obtain ⟨l, hl', _⟩ := hC [] (h6 ▸ List.mem_cons_self)
    exact absurd hl' List.not_mem_nil
  · rw [e]
    exact ⟨not_sat_false, Nat.zero_le _⟩
  · rw [ho] at h1
    omega
end CircuitLowerBound.Alg
