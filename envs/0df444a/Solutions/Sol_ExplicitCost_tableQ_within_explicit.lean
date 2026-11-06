-- Prove2me | solution 1 for ExplicitCost.tableQ_within_explicit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:34:32.512033+00:00
-- url     : https://prove2.me/submissions/af89b035-8285-42da-9078-55fcbb5ad1fe

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
import Theorems.Thm_ExplicitCost_mergedVal_eq_display
import Theorems.Thm_ExplicitCost_display_close
import Theorems.Thm_Eight_ViaGrouping_Table_lbLen_eq_Y
import Theorems.Thm_Eight_ViaGrouping_Table_tableM_runs
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_NetE_length_members
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
import Theorems.Thm_Printed_asked_isNetworkP
import Theorems.Thm_Printed_stToLists
import Theorems.Thm_Printed_tableQ_close
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
import Theorems.Thm_QueryMachines_stClose
import Theorems.Thm_QueryMachines_stSlowDown
attribute [local fun_prop] Groundwork.PolyT.length
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
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution {K g : ℕ} (hK0 : 0 < K) (N : Net g) {P B τ : ℕ} (hN : N.Is P B) (hτ : 1 ≤ τ) (x L : ℕ)
    (hG1 : ∀ γ : Fin K, K * #{a : Fin g | Paper.grouping hK0 x a = γ} ≤ 2 * g) (hY : ∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L) (γ : Fin K) {Θ : List Bool} (hΘ : Θ ∈ words ((K - 1) * L)) :
    (tableQ K g asked).Within (netOracle N) (fun _ => τ) ((netInput N P B, x), toLists K L (γ.val, Θ)) (2 ^ (P * (2 * g / K)) * (g * g * 8 + 1) * τ)
      (size (netInput N P B) + 2 * size g + 4 * P + B + 4 + 4 * (size (netInput N P B) + size x + size K + K * (2 * L + 2)) + 5 * (P * (2 * g / K)) + 2 * (B * (g * g)) + 3 * size (g * g) + 30)
      ((Value.groupClique asked.under (netInput N P B) N hK0 x L).W γ Θ) := by
  have hnet := asked_isNetworkP N hN
  obtain ⟨e1, e2, -⟩ := stToLists K L γ Θ hΘ
  have hθ : ∀ γ', γ' ≠ γ → ((fun u : Fin K => if u = γ then [] else copyAt L γ u Θ) γ').length = L := fun γ' hne => by
    simp only [if_neg hne]
    exact e2 γ' hne
  have hγ : (fun u : Fin K => if u = γ then [] else copyAt L γ u Θ) γ = [] := if_pos rfl
  have hmem : ∀ G < K, (members K g x G).length ≤ 2 * g / K := fun G hG => by
    rw [length_members hK0 x ⟨G, hG⟩, Nat.le_div_iff_mul_le hK0, Nat.mul_comm]
    exact hG1 ⟨G, hG⟩
  have hlb : ∀ G < K, ∀ G' < K, G ≠ G' → lbLen K g (asked.close (netOracle N)).toPaperNetwork (netInput N P B) x G G' ≤ L := fun G hG G' hG' hne => by
    have hne' : (⟨G, hG⟩ : Fin K) ≠ ⟨G', hG'⟩ := fun e => hne (congrArg Fin.val e)
    rw [Table.lbLen_eq_Y hnet hK0 x hne']
    exact hY _ _ hne'
  have hrun := Table.tableM_runs hnet (2 * g / K) hmem hlb hθ hγ
  rw [mergedVal_eq_display hnet hK0 x L hY γ _ hθ, display_close, ← tableQ_close] at hrun
  rw [e1]
  exact stSlowDown _ _ _ _ _ _ _ _ _ τ _ hτ ((stClose _ _ _ _ _ _ _ _ _ _).1 hrun)
end ExplicitCost
