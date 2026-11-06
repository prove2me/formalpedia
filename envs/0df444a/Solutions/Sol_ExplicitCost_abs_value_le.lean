-- Prove2me | solution 1 for ExplicitCost.abs_value_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:32:10.856726+00:00
-- url     : https://prove2.me/submissions/7a89f3af-31ec-46e2-afa4-21d1f1251ebc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_GroupingDefs
import Definitions.Def_ExplicitCost_GroupingSearch
import Definitions.Def_ExplicitCost_Cost
import Definitions.Def_Printed_GroupingEntry
import Definitions.Def_Printed_GroupingRun
import Definitions.Def_QueryMachines_CombRuns
import Definitions.Def_Value_End
import Definitions.Def_GeneralPieces_Main
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_GroupingCall
import Theorems.Thm_ClauseBound_Grid_abs_prod_le_pow
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_card_words
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_PaddedDescent_F_Eval_Form_len_le
import Theorems.Thm_Printed_abs_prod_le_pow
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution {g : ℕ} {N : Net g} {P B : ℕ} (h : N.Is P B) : |N.value| ≤ 2 ^ (g * P + g * B + g ^ 2 * B) := by
  have hm1 : (1 : ℤ) ≤ 2 ^ B := one_le_pow₀ (by norm_num)
  have hterm : ∀ z ∈ Fintype.piFinset N.S, |(∏ a, N.W a (z a)) * ∏ p ∈ pairs (Fin g), N.Ψ p.1 p.2 (z p.1) (z p.2)| ≤ (2 ^ B) ^ g * (2 ^ B) ^ (g ^ 2) := by
    intro z hz
    have hz' := Fintype.mem_piFinset.1 hz
    rw [abs_mul]
    refine mul_le_mul ?_ ?_ (abs_nonneg _) (by positivity)
    · have := abs_prod_le_pow univ (fun a => N.W a (z a)) (2 ^ B) fun a _ => (h.ii_W a _ (hz' a)).le
      rwa [Finset.card_univ, Fintype.card_fin] at this
    · refine (abs_prod_le_pow (pairs (Fin g)) (fun p => N.Ψ p.1 p.2 (z p.1) (z p.2)) (2 ^ B) fun p hp =>
        (h.ii_Ψ _ _ (ne_of_lt (mem_filter.1 hp).2) _ (hz' _) _ (hz' _)).le).trans ?_
      refine pow_le_pow_right₀ hm1 ?_
      calc #(pairs (Fin g)) ≤ #(univ : Finset (Fin g × Fin g)) := card_le_card (filter_subset _ _)
        _ = g ^ 2 := by rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, sq]
  have hcard : #(Fintype.piFinset N.S) ≤ (2 ^ P) ^ g := by
    rw [Fintype.card_piFinset]
    calc ∏ a, #(N.S a) ≤ ∏ _a : Fin g, 2 ^ P := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun a _ =>
          calc #(N.S a) ≤ #(words (N.len a)) := card_le_card fun z hz => mem_words.2 (h.len_S a z hz)
            _ = 2 ^ N.len a := card_words _
            _ ≤ 2 ^ P := Nat.pow_le_pow_right (by norm_num) (h.len_le a)
      _ = (2 ^ P) ^ g := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  unfold Net.value
  calc |∑ z ∈ Fintype.piFinset N.S, (∏ a, N.W a (z a)) * ∏ p ∈ pairs (Fin g), N.Ψ p.1 p.2 (z p.1) (z p.2)|
      ≤ ∑ z ∈ Fintype.piFinset N.S, |(∏ a, N.W a (z a)) * ∏ p ∈ pairs (Fin g), N.Ψ p.1 p.2 (z p.1) (z p.2)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _z ∈ Fintype.piFinset N.S, ((2 : ℤ) ^ B) ^ g * (2 ^ B) ^ (g ^ 2) := Finset.sum_le_sum hterm
    _ = (#(Fintype.piFinset N.S) : ℤ) * (((2 : ℤ) ^ B) ^ g * (2 ^ B) ^ (g ^ 2)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((2 : ℤ) ^ P) ^ g * (((2 : ℤ) ^ B) ^ g * (2 ^ B) ^ (g ^ 2)) := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = 2 ^ (g * P + g * B + g ^ 2 * B) := by
      rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
      congr 1
      ring
end ExplicitCost
