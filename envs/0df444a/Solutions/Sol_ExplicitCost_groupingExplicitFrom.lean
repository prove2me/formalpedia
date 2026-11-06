-- Prove2me | solution 1 for ExplicitCost.groupingExplicitFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:25:31.650368+00:00
-- url     : https://prove2.me/submissions/b93138c5-6409-4fdc-9569-6c415fd153dd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_GroupingDefs
import Definitions.Def_ExplicitCost_GroupingNumbers
import Definitions.Def_ExplicitCost_GroupingSearch
import Definitions.Def_ExplicitCost_GroupingCall
import Definitions.Def_ExplicitCost_Cost
import Definitions.Def_Printed_GroupingEntry
import Definitions.Def_Printed_GroupingRun
import Definitions.Def_Printed_Achievable
import Definitions.Def_QueryMachines_Runs
import Definitions.Def_GeneralPieces_Main
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_GroupingLemma
import Theorems.Thm_ExplicitCost_answerCall_within
import Theorems.Thm_ClauseBound_Alg_End_time_le
import Theorems.Thm_ClauseBound_Gen_Rate_size_pow_le
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_key
import Theorems.Thm_ExplicitCost_Sizes_add_three_le
import Theorems.Thm_ExplicitCost_Sizes_basic_facts
import Theorems.Thm_ExplicitCost_Sizes_search_sizes
import Theorems.Thm_ExplicitCost_Sizes_size_pow_le
import Theorems.Thm_ExplicitCost_size_groupingInput
import Theorems.Thm_GeneralPieces_Series_cf_add
import Theorems.Thm_GeneralPieces_Series_cf_neg
import Theorems.Thm_GeneralPieces_Series_cf_smul
import Theorems.Thm_GeneralPieces_Series_cf_sub
import Theorems.Thm_GeneralPieces_Series_cf_zero
import Theorems.Thm_GeneralPieces_Trim_length_bitsOf
import Theorems.Thm_GeneralPieces_Trim_length_rep
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_congr
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
import Theorems.Thm_PaddedDescent_F_Mark_InvS_size
import Theorems.Thm_Printed_mapIn_within
import Theorems.Thm_Printed_size_netInput_le
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
attribute [local simp] GeneralPieces.Series.cf_add
attribute [local simp] GeneralPieces.Series.cf_neg
attribute [local simp] GeneralPieces.Series.cf_smul
attribute [local simp] GeneralPieces.Series.cf_sub
attribute [local simp] GeneralPieces.Series.cf_zero
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


section
namespace ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed Sizes
private theorem time_le {C c₁ Kg 𝒯 n τ X : ℕ} (hX : 2 ≤ X) (hKg : 1 ≤ Kg) (hn : 1 ≤ n) (hτ : 1 ≤ τ) :
    C * Kg + (𝒯 * (n * τ * X ^ c₁ + 2) + 2) ≤ (Kg + 𝒯 * n * τ) * X ^ (C + c₁ + 12) := by
  obtain ⟨Y, hY⟩ : ∃ Y, Y = X ^ c₁ := ⟨_, rfl⟩
  have hY1 : 1 ≤ Y := hY ▸ Nat.one_le_pow _ _ (by omega)
  have hD : C + 3 ≤ X ^ (C + 12) :=
    calc C + 3 ≤ 2 ^ (C + 3) := Nat.lt_two_pow_self.le
      _ ≤ X ^ (C + 3) := Nat.pow_le_pow_left hX _
      _ ≤ X ^ (C + 12) := Nat.pow_le_pow_right (by omega) (by omega)
  have e : X ^ (C + c₁ + 12) = X ^ (C + 12) * Y := by
    rw [hY, ← pow_add]
    congr 1
    omega
  rw [← hY, e]
  have ht : 1 ≤ n * τ * Y := Nat.mul_pos (Nat.mul_pos hn hτ) hY1
  have a1 : 𝒯 * (n * τ * Y + 2) ≤ 𝒯 * (3 * (n * τ * Y)) := Nat.mul_le_mul_left _ (by omega)
  have a2 : (C + 2) * Kg = C * Kg + 2 * Kg := by ring
  have a3 : (C + 2) * Kg ≤ (C + 2) * Kg * Y := Nat.le_mul_of_pos_right _ hY1
  have e1 : (C + 2) * Kg * Y + 𝒯 * (3 * (n * τ * Y)) + (Kg * Y + C * (𝒯 * n * τ * Y)) = (C + 3) * ((Kg + 𝒯 * n * τ) * Y) := by ring
  calc C * Kg + (𝒯 * (n * τ * Y + 2) + 2) ≤ (C + 3) * ((Kg + 𝒯 * n * τ) * Y) := by omega
    _ ≤ X ^ (C + 12) * ((Kg + 𝒯 * n * τ) * Y) := Nat.mul_le_mul_right _ hD
    _ = (Kg + 𝒯 * n * τ) * (X ^ (C + 12) * Y) := by ring
private theorem real_time_le {T K g P B 𝒯 τ C₁ : ℕ} (h : T ≤ (K ^ g + 𝒯 * 2 ^ (P * (2 * g / K)) * τ) * (g * (P + B)) ^ C₁) :
    (T : ℝ) ≤ ((K : ℝ) ^ g + 𝒯 * (2 : ℝ) ^ (2 * (g : ℝ) * P / K) * τ) * ((g : ℝ) * (P + B)) ^ C₁ := by
  have h1 : (T : ℝ) ≤ (((K ^ g + 𝒯 * 2 ^ (P * (2 * g / K)) * τ) * (g * (P + B)) ^ C₁ : ℕ) : ℝ) := by exact_mod_cast h
  have hexp : ((P * (2 * g / K) : ℕ) : ℝ) ≤ 2 * (g : ℝ) * P / K := by
    have hd : ((2 * g / K : ℕ) : ℝ) ≤ ((2 * g : ℕ) : ℝ) / K := Nat.cast_div_le
    calc ((P * (2 * g / K) : ℕ) : ℝ) = (P : ℝ) * ((2 * g / K : ℕ) : ℝ) := Nat.cast_mul _ _
      _ ≤ (P : ℝ) * (((2 * g : ℕ) : ℝ) / K) := mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg _)
      _ = 2 * (g : ℝ) * P / K := by
        push_cast
        ring
  have h2 : (2 : ℝ) ^ (P * (2 * g / K)) ≤ (2 : ℝ) ^ (2 * (g : ℝ) * P / K) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le one_le_two hexp
  have e : (((K ^ g + 𝒯 * 2 ^ (P * (2 * g / K)) * τ) * (g * (P + B)) ^ C₁ : ℕ) : ℝ) = ((K : ℝ) ^ g + 𝒯 * (2 : ℝ) ^ (P * (2 * g / K)) * τ) * ((g : ℝ) * (P + B)) ^ C₁ := by
    push_cast
    ring
  rw [e] at h1
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  exact add_le_add_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) _
end ExplicitCost
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed Sizes
namespace ExplicitCost
theorem _root_.solution : GroupingExplicitFrom := by
  classical
  intro hW hL hEC hS hMono hSlow hSub
  obtain ⟨C, hC⟩ := hW
  obtain ⟨c₁, hc₁⟩ := hEC
  refine ⟨C + c₁ + 12, fun α E arg a b K g N P B τ 𝒯 SE hK hg ha hab hN hτ hCases hE => ?_⟩
  have hK0 : 0 < K := by omega
  have hb : 0 < b := by omega
  have hζ0 : (0 : ℝ) < (a : ℝ) / b := div_pos (by exact_mod_cast ha) (by exact_mod_cast hb)
  have hζ1 : (a : ℝ) / b ≤ 1 := (div_le_one (by exact_mod_cast hb)).2 (by exact_mod_cast hab)
  obtain ⟨hKg, hLle⟩ := hS K g _ P N.c hK hg hζ0 hζ1 hN.P_pos hN.i hCases
  have hgP : 1 ≤ g * P := Nat.mul_pos (by omega) hN.P_pos
  have hL2 : AppRunningTime.Lof K g ((a : ℝ) / b) P N.U ≤ 2 * (g * P) := le_trans hLle (by omega)
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t = 2 ^ (P * (2 * g / K)) * τ * (g * (P + B)) ^ c₁ := ⟨_, rfl⟩
  obtain ⟨x, hx, -, h1, h2, hcall⟩ := hC a b K g hK0 N P B (𝒯 * (t + 2) + 2) hK hg ha hab hN hCases
  have hans := answerCall_within hL hSlow hSub E arg hK0 hb hab hN hE (hc₁ K g hK0 N P B τ hKg hN hτ x hx _ hL2 h1 h2)
  rw [← ht] at hans
  -- the oracle that answers the call of x, and nothing else
  have hup := hcall (fun y => if y = callOf (groupingInput a b K N P B, x) then
    some (Value.groupClique asked.under (netInput N P B) N hK0 x (AppRunningTime.Lof K g ((a : ℝ) / b) P N.U)).value else none) (if_pos rfl)
  have hsub := hSub _ _ _ _ GroupingInput _ _ groupingCall (answerCall E arg) _ (netOracle N) (fun _ => 𝒯 * (t + 2) + 2) (fun _ => τ) (groupingInput a b K N P B) _ _ _
    (size (groupingInput a b K N P B, x) + SE + (g * (P + B)) ^ c₁ + 1) _ (fun _ => 𝒯 * (t + 2)) hup
    (fun y v hy => by
      by_cases e : y = callOf (groupingInput a b K N P B, x)
      · rw [if_pos e] at hy
        obtain rfl := Option.some.inj hy
        rw [e]
        exact hans
      · rw [if_neg e] at hy
        cases hy)
    (fun _ => le_rfl)
  obtain ⟨own, Lq, hr, hle⟩ := mapIn_within (f := fun c : GroupingInput => (c, c)) hsub
  have hX := (basic_facts (hK0.trans_le hKg) hN.P_pos hN.B_pos).1
  refine ⟨C * K ^ g + (𝒯 * (t + 2) + 2), ⟨own, Lq, hMono _ _ _ _ _ _ _ _ _ _ _ _ _ hr le_rfl ?_, hle⟩, real_time_le ?_⟩
  · -- the sizes of the states
    obtain ⟨Z, hZ⟩ : ∃ Z, Z = g * (P + B) + size (a, b) := ⟨_, rfl⟩
    rw [← hZ]
    have hZ2 : 2 ≤ Z := by omega
    have m1 : Z ^ 10 ≤ Z ^ (C + c₁ + 10) := Nat.pow_le_pow_right (by omega) (by omega)
    have m2 : Z ^ C ≤ Z ^ (C + c₁ + 10) := Nat.pow_le_pow_right (by omega) (by omega)
    have m3 : (g * (P + B)) ^ c₁ ≤ Z ^ (C + c₁ + 10) := (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) (by omega))
    have s1 := search_sizes (s := size (a, b)) hK0 hKg hN.P_pos hN.B_pos (size_netInput_le N hN) (size_pow_le hKg)
    have s4 := size_groupingInput a b K N P B
    have s5 : size x ≤ size (K ^ g) := by
      simp only [size_nat]
      exact Nat.succ_le_succ (Nat.size_le_size hx.le)
    have s6 : size (groupingInput a b K N P B, x) = size (groupingInput a b K N P B) + size x := rfl
    rw [← hZ] at s1
    have key := add_three_le (n := C + c₁ + 10) (u := 2 * size (groupingInput a b K N P B) + size x + 2) (v := Z ^ C) (w := (g * (P + B)) ^ c₁) hZ2 (by omega) m2 m3
    have e : C + c₁ + 12 = C + c₁ + 10 + 2 := by omega
    rw [e]
    omega
  · rw [ht]
    exact time_le (by omega) (Nat.one_le_pow _ _ hK0) Nat.one_le_two_pow hτ
end ExplicitCost
