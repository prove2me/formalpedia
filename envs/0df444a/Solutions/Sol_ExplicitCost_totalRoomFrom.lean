-- Prove2me | solution 1 for ExplicitCost.totalRoomFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:51:26.023917+00:00
-- url     : https://prove2.me/submissions/4299fde9-6d97-4675-8896-ad4833571bd7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Chain
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_TotalRoom
import Theorems.Thm_ExplicitCost_towerSize_le
import Theorems.Thm_ExplicitCost_bitsAt_self
import Theorems.Thm_ExplicitCost_lamAt_self
import Theorems.Thm_ExplicitCost_two_pow_le_K
import Theorems.Thm_GeneralPieces_Trim_length_bitsOf
import Theorems.Thm_GeneralPieces_Trim_length_rep
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_TM_Run_trans
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
import Theorems.Thm_Groundwork_TM_update_withIO
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
import Theorems.Thm_QueryMachines_QueryMachine_close_bind
import Theorems.Thm_QueryMachines_QueryMachine_close_both
import Theorems.Thm_QueryMachines_QueryMachine_close_branch
import Theorems.Thm_QueryMachines_QueryMachine_close_const
import Theorems.Thm_QueryMachines_QueryMachine_close_foldRange
import Theorems.Thm_QueryMachines_QueryMachine_close_foldWhile
import Theorems.Thm_QueryMachines_QueryMachine_close_gated
import Theorems.Thm_QueryMachines_QueryMachine_close_ite
import Theorems.Thm_QueryMachines_QueryMachine_close_lift
import Theorems.Thm_QueryMachines_QueryMachine_close_mapAsk
import Theorems.Thm_QueryMachines_QueryMachine_close_mapIn
import Theorems.Thm_QueryMachines_QueryMachine_close_mapOut
import Theorems.Thm_QueryMachines_QueryMachine_close_optBind
import Theorems.Thm_QueryMachines_QueryMachine_close_prodRange
import Theorems.Thm_QueryMachines_QueryMachine_close_query
import Theorems.Thm_QueryMachines_QueryMachine_close_subst
import Theorems.Thm_QueryMachines_QueryMachine_close_sumRange
attribute [local simp] GeneralPieces.Trim.length_bitsOf
attribute [local simp] GeneralPieces.Trim.length_rep
attribute [local simp] Groundwork.Host.upd_none
attribute [local simp] Groundwork.Host.withIO_none
attribute [local simp] Groundwork.Host.withIO_some
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
attribute [local simp] Groundwork.TM.update_withIO
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
attribute [local simp] QueryMachines.QueryMachine.close_bind
attribute [local simp] QueryMachines.QueryMachine.close_both
attribute [local simp] QueryMachines.QueryMachine.close_branch
attribute [local simp] QueryMachines.QueryMachine.close_const
attribute [local simp] QueryMachines.QueryMachine.close_foldRange
attribute [local simp] QueryMachines.QueryMachine.close_foldWhile
attribute [local simp] QueryMachines.QueryMachine.close_gated
attribute [local simp] QueryMachines.QueryMachine.close_ite
attribute [local simp] QueryMachines.QueryMachine.close_lift
attribute [local simp] QueryMachines.QueryMachine.close_mapAsk
attribute [local simp] QueryMachines.QueryMachine.close_mapIn
attribute [local simp] QueryMachines.QueryMachine.close_mapOut
attribute [local simp] QueryMachines.QueryMachine.close_optBind
attribute [local simp] QueryMachines.QueryMachine.close_prodRange
attribute [local simp] QueryMachines.QueryMachine.close_query
attribute [local simp] QueryMachines.QueryMachine.close_subst
attribute [local simp] QueryMachines.QueryMachine.close_sumRange



set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed QueryMachines Finset
namespace ExplicitCost
theorem _root_.solution : TotalRoomFrom := by
  intro hB hLv c C
  refine ⟨C + 6, fun ρ x₀ l lam B h1 h2 h3 h4 h5 h6 h7 => ?_⟩
  have hN : Numbers ρ c x₀ lam B := ⟨h1, h2, h3, h4, h5, h6, h7⟩
  obtain ⟨X, hX⟩ : ∃ X, X = K x₀ l * (lam + B) := ⟨_, rfl⟩
  have hXl : baseAt ρ c x₀ l lam B l = X := by rw [hX, baseAt, lamAt_self, bitsAt_self]
  have hKl := (hLv c x₀ l 0 h4 h5 (Nat.zero_le l)).2
  have hK3 : 3 ≤ K x₀ l := by
    have a : 2 ^ 2 ≤ 2 ^ x₀ := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := two_pow_le_K x₀ l
    omega
  have hlK : l < K x₀ l := (Nat.lt_two_pow_self (n := l)).trans_le ((Nat.pow_le_pow_left (by omega) l).trans hKl)
  have h2K : K x₀ l * 2 ≤ X := by rw [hX]; exact Nat.mul_le_mul_left _ (by omega)
  have hX1 : 1 ≤ X := by omega
  -- X_j ≤ X^{(c+5)^{ℓ−j}}
  have s1 : ∀ k j, j + k = l → baseAt ρ c x₀ l lam B j ≤ X ^ (c + 5) ^ k := by
    intro k
    induction k with
    | zero =>
      intro j hj
      obtain rfl : j = l := by omega
      rw [hXl]
      simp
    | succ k ih =>
      intro j hj
      calc baseAt ρ c x₀ l lam B j ≤ baseAt ρ c x₀ l lam B (j + 1) ^ (c + 5) := hB ρ c x₀ l lam B j hN (by omega)
        _ ≤ (X ^ (c + 5) ^ k) ^ (c + 5) := Nat.pow_le_pow_left (ih (j + 1) (by omega)) _
        _ = X ^ (c + 5) ^ (k + 1) := by rw [← pow_mul, pow_succ]
  -- X_j^C ≤ X^{CK_ℓ}
  have s2 : ∀ j ∈ range (l + 1), (K x₀ j * (lamAt ρ c x₀ l lam B j + bitsAt ρ c x₀ l lam B j)) ^ C ≤ X ^ (C * K x₀ l) := by
    intro j hj
    have hjl : j ≤ l := by have := mem_range.1 hj; omega
    have a1 : (c + 5) ^ (l - j) ≤ K x₀ l := (Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)).trans hKl
    calc (K x₀ j * (lamAt ρ c x₀ l lam B j + bitsAt ρ c x₀ l lam B j)) ^ C ≤ (X ^ (c + 5) ^ (l - j)) ^ C := Nat.pow_le_pow_left (s1 (l - j) j (by omega)) _
      _ ≤ (X ^ K x₀ l) ^ C := Nat.pow_le_pow_left (Nat.pow_le_pow_right hX1 a1) _
      _ = X ^ (C * K x₀ l) := by rw [← pow_mul, Nat.mul_comm]
  have s3 : roomAll C ρ c x₀ l lam B ≤ (l + 3) * X ^ (C * K x₀ l) := by
    have := Finset.sum_le_card_nsmul _ _ _ s2
    rw [card_range, smul_eq_mul] at this
    exact this.trans (Nat.mul_le_mul_right _ (by omega))
  have s4 := towerSize_le (l := l) rfl (Nat.pow_pos hX1) s3
  have s5 : 5 * ((l + 3) ^ 3 * X ^ (C * K x₀ l)) ≤ X ^ ((C + 6) * K x₀ l) := by
    have b1 : (l + 3) ^ 3 ≤ X ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have b2 : 5 ≤ X ^ 3 := by
      have : 2 ^ 3 ≤ X ^ 3 := Nat.pow_le_pow_left (by omega) 3
      omega
    calc 5 * ((l + 3) ^ 3 * X ^ (C * K x₀ l)) ≤ X ^ 3 * (X ^ 3 * X ^ (C * K x₀ l)) := Nat.mul_le_mul b2 (Nat.mul_le_mul_right _ b1)
      _ = X ^ (6 + C * K x₀ l) := by ring
      _ ≤ X ^ ((C + 6) * K x₀ l) := Nat.pow_le_pow_right hX1 (by
          have : (C + 6) * K x₀ l = C * K x₀ l + 6 * K x₀ l := by ring
          omega)
  have s6 := s4.trans s5
  unfold sizeBound
  rw [hX] at s6
  exact_mod_cast s6
end ExplicitCost
