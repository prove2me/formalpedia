-- Prove2me | solution 1 for ExplicitCost.groupingWithCallFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:58:30.112515+00:00
-- url     : https://prove2.me/submissions/ba13cc79-de86-43d2-ac46-0363f3b7ff88

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
import Theorems.Thm_ExplicitCost_size_value_le
import Theorems.Thm_ExplicitCost_Sizes_add_three_le
import Theorems.Thm_ClauseBound_Gen_Rate_size_pow_le
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_key
import Theorems.Thm_ExplicitCost_Mirrors_mono
import Theorems.Thm_ExplicitCost_Sizes_basic_facts
import Theorems.Thm_ExplicitCost_Sizes_search_sizes
import Theorems.Thm_ExplicitCost_Sizes_size_pow_le
import Theorems.Thm_ExplicitCost_Sizes_sq_le_pow
import Theorems.Thm_ExplicitCost_size_groupingInput
import Theorems.Thm_GeneralPieces_Ring_Bd_mono
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
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
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
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_Printed_AchievedBy_mono
import Theorems.Thm_Printed_asked_isNetworkP
import Theorems.Thm_Printed_optBind_within
import Theorems.Thm_Printed_size_netInput_le
import Theorems.Thm_QueryMachines_QueryMachine_Reaches_mono
import Theorems.Thm_QueryMachines_QueryMachine_Runs_mono
import Theorems.Thm_QueryMachines_QueryMachine_WithinFrom_mono
import Theorems.Thm_QueryMachines_QueryMachine_Within_mono
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
import Theorems.Thm_QueryMachines_stQueryRuns
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InRateTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono
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
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
namespace Sizes
end Sizes
open Sizes
private theorem value_sizes {g P B : ℕ} (s : ℕ) (hg : 1 ≤ g) (hP : 1 ≤ P) (hB : 1 ≤ B) : g * P + g * B + g ^ 2 * B + 2 ≤ (g * (P + B) + s) ^ 10 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := basic_facts hg hP hB
  refine le_trans ?_ (sq_le_pow (X := g * (P + B) + s) (by omega))
  have e : (g * (P + B) + s) * (g * (P + B) + s) = g * (P + B) * (g * (P + B)) + 2 * (g * (P + B) * s) + s * s := by ring
  have e1 : g * P + g * B = g * (P + B) := by ring
  have e2 : g ^ 2 * B = B * (g * g) := by ring
  rw [e, e1, e2]
  omega
end ExplicitCost
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
open Sizes
namespace ExplicitCost
theorem _root_.solution : GroupingWithCallFrom := by
  intro hF hSC hS hV
  obtain ⟨C, hC⟩ := hSC
  refine ⟨C + 12, fun a b K g hK0 N P B tc hK hg ha hab hN hCases => ?_⟩
  have hb : 0 < b := by omega
  have hζ0 : (0 : ℝ) < (a : ℝ) / b := div_pos (by exact_mod_cast ha) (by exact_mod_cast hb)
  have hζ1 : (a : ℝ) / b ≤ 1 := (div_le_one (by exact_mod_cast hb)).2 (by exact_mod_cast hab)
  obtain ⟨hKg, -⟩ := hS K g _ P N.c hK hg hζ0 hζ1 hN.P_pos hN.i hCases
  obtain ⟨x, hx, hfind, h1, h2⟩ := hF a b K g hK0 N P B hK hg ha hab hN hCases
  refine ⟨x, hx, hfind, h1, h2, fun O hO => ?_⟩
  have hval : (Value.groupClique asked.under (netInput N P B) N hK0 x (AppRunningTime.Lof K g ((a : ℝ) / b) P N.U)).value = N.value :=
    hV NetInput g K hK0 (asked.close (netOracle N)) (netInput N P B) N P B 1 _ (asked_isNetworkP N hN) x _ h2
  rw [hval] at hO
  have hsearch := hC a b K g N P B x hK0 hKg hN hfind
  have hquery : (QueryMachine.query callOf : QueryMachine CliqueCall ℤ (GroupingInput × ℕ) ℤ).Within O (fun _ => tc) (groupingInput a b K N P B, x) tc
      (max (size (groupingInput a b K N P B, x)) (size N.value) + 1) N.value :=
    ⟨0, [callOf (groupingInput a b K N P B, x)], stQueryRuns _ _ _ callOf O _ _ hO, by simp⟩
  refine (optBind_within (dflt := zeroOf) hsearch hquery).mono ?_ ?_
  · have : 1 ≤ K ^ g := Nat.one_le_pow _ _ hK0
    have e : (C + 12) * K ^ g = C * K ^ g + 12 * K ^ g := by ring
    omega
  · obtain ⟨Z, hZ⟩ : ∃ Z, Z = g * (P + B) + size (a, b) := ⟨_, rfl⟩
    rw [← hZ]
    have hX := (basic_facts (hK0.trans_le hKg) hN.P_pos hN.B_pos).1
    have hZ2 : 2 ≤ Z := by omega
    have hm : Z ^ 10 ≤ Z ^ (C + 10) := Nat.pow_le_pow_right (by omega) (by omega)
    have hm' : Z ^ C ≤ Z ^ (C + 10) := Nat.pow_le_pow_right (by omega) (by omega)
    have s1 := search_sizes (s := size (a, b)) hK0 hKg hN.P_pos hN.B_pos (size_netInput_le N hN) (size_pow_le hKg)
    have s2 := value_sizes (size (a, b)) (hK0.trans_le hKg) hN.P_pos hN.B_pos
    have s3 := size_value_le hN
    have s4 := size_groupingInput a b K N P B
    have s5 : size x ≤ size (K ^ g) := by
      simp only [size_nat]
      exact Nat.succ_le_succ (Nat.size_le_size hx.le)
    have s6 : size (groupingInput a b K N P B, x) = size (groupingInput a b K N P B) + size x := rfl
    rw [← hZ] at s1 s2
    have key := add_three_le (n := C + 10) (u := size (groupingInput a b K N P B) + size x + 4) (v := Z ^ C) (w := size N.value) hZ2 (by omega) hm' (by omega)
    have e : C + 12 = C + 10 + 2 := by omega
    rw [e]
    omega
end ExplicitCost
