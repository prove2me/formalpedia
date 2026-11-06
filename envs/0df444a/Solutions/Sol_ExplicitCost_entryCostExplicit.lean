-- Prove2me | solution 1 for ExplicitCost.entryCostExplicit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:42:14.876203+00:00
-- url     : https://prove2.me/submissions/1dabef97-cb7c-41be-9506-65cd8b748e2c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_EntryDefs
import Definitions.Def_ExplicitCost_SameRuns
import Definitions.Def_Printed_GroupingEntry
import Definitions.Def_Printed_Close
import Definitions.Def_Printed_Coding
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_Cost
import Theorems.Thm_ExplicitCost_tableQ_within_explicit
import Theorems.Thm_ExplicitCost_Sizes_sq_le_pow
import Theorems.Thm_ExplicitCost_Sizes_basic_facts
import Theorems.Thm_ExplicitCost_Mirrors_mono
import Theorems.Thm_ExplicitCost_Mirrors_within
import Theorems.Thm_ExplicitCost_mirrors_entryData
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Prog_size_nat_le
import Theorems.Thm_Groundwork_RebalanceArith_size_le
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
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
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_Printed_AchievedBy_mono
import Theorems.Thm_Printed_abs_display_lt
import Theorems.Thm_Printed_asked_isNetworkP
import Theorems.Thm_Printed_size_netInput_le
import Theorems.Thm_Printed_stToLists
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
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InRateTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono
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
private theorem factor_le {g P B : ℕ} (hg : 1 ≤ g) (hP : 1 ≤ P) (hB : 1 ≤ B) : g * g * 8 + 1 ≤ (g * (P + B)) ^ 10 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := basic_facts hg hP hB
  refine le_trans ?_ (sq_le_pow (X := g * (P + B)) (by omega))
  omega
private theorem states_le {K g P B x L sc : ℕ} (hK0 : 0 < K) (hKg : K ≤ g) (hP : 1 ≤ P) (hB : 1 ≤ B) (hx : x < K ^ g) (hL : L ≤ 2 * (g * P)) (hsc : sc ≤ (4 * g ^ 2 + 6 * g + 6) * (P + B)) :
    sc + 2 * size g + 4 * P + B + 4 + 4 * (sc + size x + size K + K * (2 * L + 2)) + 5 * (P * (2 * g / K)) + 2 * (B * (g * g)) + 3 * size (g * g) + 30 + 4 * (2 * K + 2 * g + 2) ≤ (g * (P + B)) ^ 10 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := basic_facts (hK0.trans_le hKg) hP hB
  refine le_trans ?_ (sq_le_pow (X := g * (P + B)) (by omega))
  have s1 : sc ≤ 4 * (g * g * (P + B)) + 6 * (g * (P + B)) + 6 * (P + B) := by
    have : (4 * g ^ 2 + 6 * g + 6) * (P + B) = 4 * (g * g * (P + B)) + 6 * (g * (P + B)) + 6 * (P + B) := by ring
    omega
  have s2 := size_nat_le g
  have s3 := size_nat_le K
  have s4 := size_nat_le (g * g)
  have s5 : size x ≤ g * g + 1 := by
    rw [size_nat]
    refine Nat.succ_le_succ (Nat.size_le.2 (hx.trans_le ?_))
    calc K ^ g ≤ (2 ^ g) ^ g := Nat.pow_le_pow_left (hKg.trans Nat.lt_two_pow_self.le) g
      _ = 2 ^ (g * g) := (pow_mul 2 g g).symm
  have s6 : K * (2 * L + 2) ≤ 4 * (g * g * P) + 2 * g := by
    calc K * (2 * L + 2) ≤ g * (2 * (2 * (g * P)) + 2) := Nat.mul_le_mul hKg (by omega)
      _ = 4 * (g * g * P) + 2 * g := by ring
  have s7 : P * (2 * g / K) ≤ 2 * (g * (P + B)) := by
    calc P * (2 * g / K) ≤ (P + B) * (2 * g) := Nat.mul_le_mul (by omega) (Nat.div_le_self _ _)
      _ = 2 * (g * (P + B)) := by ring
  omega
end ExplicitCost
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
open Sizes
namespace ExplicitCost
theorem _root_.solution : EntryCostExplicit := by
  refine ⟨10, fun K g hK0 N P B τ hKg hN hτ x hx L hL hG1 hY γ Θ hΘ => ⟨?_, ?_⟩⟩
  · refine ((mirrors_entryData K g).within (tableQ_within_explicit hK0 N hN hτ x L hG1 hY γ hΘ)).mono ?_ (states_le hK0 hKg hN.P_pos hN.B_pos hx hL (size_netInput_le N hN))
    calc 2 ^ (P * (2 * g / K)) * (g * g * 8 + 1) * τ = 2 ^ (P * (2 * g / K)) * τ * (g * g * 8 + 1) := by ring
      _ ≤ 2 ^ (P * (2 * g / K)) * τ * (g * (P + B)) ^ 10 := Nat.mul_le_mul_left _ (factor_le (hK0.trans_le hKg) hN.P_pos hN.B_pos)
  · obtain ⟨-, e2, -⟩ := stToLists K L γ Θ hΘ
    exact abs_display_lt (asked_isNetworkP N hN) hK0 (hK0.trans_le hKg) x L hG1 hY γ (fun u : Fin K => if u = γ then [] else copyAt L γ u Θ) fun γ' hne => by
      simp only [if_neg hne]
      exact e2 γ' hne
end ExplicitCost
