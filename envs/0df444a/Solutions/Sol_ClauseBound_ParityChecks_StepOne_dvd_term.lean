-- Prove2me | solution 1 for ClauseBound.ParityChecks.StepOne.dvd_term
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:10:06.702422+00:00
-- url     : https://prove2.me/submissions/3c2b8877-c9fe-4851-8795-fd98c90133cb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_ClauseBound_ParityChecks_StepOne
import Theorems.Thm_ClauseBound_ParityChecks_StepOne_two_pow_dvd_sig
import Theorems.Thm_ClauseBound_ParityChecks_StepOne_two_pow_dvd_neg_two_pow

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.StepOne
open Finset _root_.ParityChecks
variable {E : Type} {r : ℕ}
namespace ClauseBound.ParityChecks.StepOne
theorem _root_.solution {J₁ J₂ : Finset (Fin r)} (A : Fin r → Finset E) {S : Fin r → Finset E} (hS : S ∈ Fintype.piFinset (dom A (J₁ ∪ J₂))) {ν : ℕ}
    (hν : ν + #J₁ ≤ ∑ j, #(S j)) : (2 : ℤ) ^ ν ∣ ∏ j, fac J₁ J₂ j (S j) := by
  have h1 : ∀ j : Fin r, (2 : ℤ) ^ (#(S j) - if j ∈ J₁ then 1 else 0) ∣ fac J₁ J₂ j (S j) := by
    intro j
    unfold fac
    by_cases h1 : j ∈ J₁
    · simp only [if_pos h1]
      exact two_pow_dvd_sig _
    · by_cases h2 : j ∈ J₂
      · simp only [if_neg h1, if_pos h2, Nat.sub_zero]
        exact two_pow_dvd_neg_two_pow _
      · have h3 : j ∉ J₁ ∪ J₂ := fun h => (mem_union.1 h).elim h1 h2
        have h4 := Fintype.mem_piFinset.1 hS j
        rw [dom, if_neg h3, mem_singleton] at h4
        simp only [if_neg h1, if_neg h2, h4, card_empty, Nat.sub_zero, pow_zero]
        exact one_dvd _
  have h2 : ∑ j, #(S j) ≤ ∑ j : Fin r, (#(S j) - if j ∈ J₁ then 1 else 0) + #J₁ := by
    have h3 : #J₁ = ∑ j : Fin r, if j ∈ J₁ then 1 else 0 := by
      rw [sum_boole, filter_mem_eq_inter, univ_inter, Nat.cast_id]
    rw [h3, ← sum_add_distrib]
    exact sum_le_sum fun j _ => by omega
  refine (pow_dvd_pow 2 (by omega : ν ≤ ∑ j : Fin r, (#(S j) - if j ∈ J₁ then 1 else 0))).trans ?_
  rw [← prod_pow_eq_pow_sum]
  exact prod_dvd_prod_of_dvd _ _ fun j _ => h1 j
end ClauseBound.ParityChecks.StepOne
