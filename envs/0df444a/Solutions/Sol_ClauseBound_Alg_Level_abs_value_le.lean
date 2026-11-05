-- Prove2me | solution 1 for ClauseBound.Alg.Level.abs_value_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:51:59.431959+00:00
-- url     : https://prove2.me/submissions/5c732ecc-bb7e-4e75-a96d-db15e19135cc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_RebalG
import Definitions.Def_PaddedDescent_Col_Good
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_Table
import Definitions.Def_ClauseBound_Alg_Level
import Theorems.Thm_ClauseBound_Alg_Level_card_add_card_pairs_le
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_TM_beq_LR
import Theorems.Thm_Groundwork_TM_beq_RL
import Theorems.Thm_Groundwork_TM_beq_bL
import Theorems.Thm_Groundwork_TM_beq_bR
import Theorems.Thm_Groundwork_TM_length_mirror
import Theorems.Thm_Groundwork_TM_st4_cnt
import Theorems.Thm_Groundwork_TM_st4_src
import Theorems.Thm_Groundwork_TM_st4_t1
import Theorems.Thm_Groundwork_TM_st4_t2
import Theorems.Thm_Groundwork_TM_st_a
import Theorems.Thm_Groundwork_TM_st_b
import Theorems.Thm_Groundwork_TM_st_cnt
import Theorems.Thm_Groundwork_TM_st_main
import Theorems.Thm_Groundwork_TM_upd4_cnt
import Theorems.Thm_Groundwork_TM_upd4_src
import Theorems.Thm_Groundwork_TM_upd4_t1
import Theorems.Thm_Groundwork_TM_upd4_t2
import Theorems.Thm_Groundwork_TM_upd_a
import Theorems.Thm_Groundwork_TM_upd_b
import Theorems.Thm_Groundwork_TM_upd_main
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_size_bool
import Theorems.Thm_Groundwork_size_inl
import Theorems.Thm_Groundwork_size_inr
import Theorems.Thm_Groundwork_size_int
import Theorems.Thm_Groundwork_size_list
import Theorems.Thm_Groundwork_size_nat
import Theorems.Thm_Groundwork_size_none
import Theorems.Thm_Groundwork_size_prod
import Theorems.Thm_Groundwork_size_some
import Theorems.Thm_Groundwork_size_unit
attribute [local simp] Groundwork.TM.beq_LR
attribute [local simp] Groundwork.TM.beq_RL
attribute [local simp] Groundwork.TM.beq_bL
attribute [local simp] Groundwork.TM.beq_bR
attribute [local simp] Groundwork.TM.length_mirror
attribute [local simp] Groundwork.TM.st4_cnt
attribute [local simp] Groundwork.TM.st4_src
attribute [local simp] Groundwork.TM.st4_t1
attribute [local simp] Groundwork.TM.st4_t2
attribute [local simp] Groundwork.TM.st_a
attribute [local simp] Groundwork.TM.st_b
attribute [local simp] Groundwork.TM.st_cnt
attribute [local simp] Groundwork.TM.st_main
attribute [local simp] Groundwork.TM.upd4_cnt
attribute [local simp] Groundwork.TM.upd4_src
attribute [local simp] Groundwork.TM.upd4_t1
attribute [local simp] Groundwork.TM.upd4_t2
attribute [local simp] Groundwork.TM.upd_a
attribute [local simp] Groundwork.TM.upd_b
attribute [local simp] Groundwork.TM.upd_main
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words
attribute [local simp] Groundwork.size_bool
attribute [local simp] Groundwork.size_inl
attribute [local simp] Groundwork.size_inr
attribute [local simp] Groundwork.size_int
attribute [local simp] Groundwork.size_list
attribute [local simp] Groundwork.size_nat
attribute [local simp] Groundwork.size_none
attribute [local simp] Groundwork.size_prod
attribute [local simp] Groundwork.size_some
attribute [local simp] Groundwork.size_unit



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Level
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F Finset
namespace ClauseBound.Alg.Level
theorem _root_.solution {J σ τ : Type} [Fintype J] [LinearOrder J] (N : Network J σ τ) {n P B : ℕ}
    (h : N.Sized P B) (hn : ∀ a, #(N.S a) ≤ 2 ^ n) :
    |N.value| ≤ 2 ^ (Fintype.card J * n + Fintype.card J * Fintype.card J * B) := by
  unfold Network.value
  have hW : ∀ z : J → σ, |∏ a, N.W a (z a)| ≤ (2 ^ B) ^ Fintype.card J := by
    intro z
    rw [Finset.abs_prod]
    calc _ ≤ ∏ _a : J, (2 : ℤ) ^ B := Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun a _ => h.abs_W a _
      _ = _ := by rw [Finset.prod_const, card_univ]
  have hΨ : ∀ z : J → σ, |∏ p ∈ pairs J, N.Ψ p.1 p.2 (z p.1) (z p.2)| ≤ (2 ^ B) ^ #(pairs J) := by
    intro z
    rw [Finset.abs_prod]
    calc _ ≤ ∏ _p ∈ pairs J, (2 : ℤ) ^ B := Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun p hp =>
          h.abs_Ψ _ _ _ _ (ne_of_lt (by simpa [pairs] using hp))
      _ = ((2 : ℤ) ^ B) ^ #(pairs J) := by rw [Finset.prod_const]
  have hS : (#(Fintype.piFinset N.S) : ℤ) ≤ (2 ^ n) ^ Fintype.card J := by
    rw [Fintype.card_piFinset]
    have : ∏ a, #(N.S a) ≤ ∏ _a : J, 2 ^ n := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun a _ => hn a
    rw [Finset.prod_const, card_univ] at this
    exact_mod_cast this
  calc _ ≤ ∑ z ∈ Fintype.piFinset N.S, |(∏ a, N.W a (z a)) * ∏ p ∈ pairs J, N.Ψ p.1 p.2 (z p.1) (z p.2)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _z ∈ Fintype.piFinset N.S, ((2 : ℤ) ^ B) ^ Fintype.card J * ((2 : ℤ) ^ B) ^ #(pairs J) := by
        refine Finset.sum_le_sum fun z _ => ?_
        rw [abs_mul]
        exact mul_le_mul (hW z) (hΨ z) (abs_nonneg _) (by positivity)
    _ = (#(Fintype.piFinset N.S) : ℤ) * (((2 : ℤ) ^ B) ^ Fintype.card J * ((2 : ℤ) ^ B) ^ #(pairs J)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 ^ n) ^ Fintype.card J * (((2 : ℤ) ^ B) ^ Fintype.card J * ((2 : ℤ) ^ B) ^ #(pairs J)) :=
        mul_le_mul_of_nonneg_right hS (by positivity)
    _ = 2 ^ (Fintype.card J * n + (Fintype.card J + #(pairs J)) * B) := by
        rw [← pow_add, ← pow_mul, ← pow_mul, ← pow_add]
        congr 1
        ring
    _ ≤ _ := pow_le_pow_right₀ (by norm_num)
        (Nat.add_le_add_left (Nat.mul_le_mul_right _ (card_add_card_pairs_le J)) _)
end ClauseBound.Alg.Level
