-- Prove2me | solution 1 for ExplicitCost.parent_arith
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:18:57.276615+00:00
-- url     : https://prove2.me/submissions/7235c09f-ed6c-43c9-86e0-c3e71b5f42be

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CallParts
import Definitions.Def_ClauseBound_Gen_RateAux
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_ParentSize
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
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution {X m c K g lam B R sy sx sl : ℕ} (hX : 8 ≤ X) (hm : m ≤ X ^ c) (hK : K ≤ X) (hg : g ≤ X) (hlam : 2 * lam ≤ X) (hB : B ≤ X) (hR : R ≤ X * X) (hsy : sy ≤ m * R + 1) (hsx : sx ≤ X + 1)
    (hsl : sl ≤ (m * (m + 1 + 1) + 1) + ((m * (2 * lam + 1 + 1) + 1) + (m * (2 * lam + 1 + 1) + 1))) :
    (2 * K + 1 + (2 * g + 1)) + ((2 * lam + 1 + (2 * B + 1)) + (sl + (1 + (sy + sx)))) ≤ X ^ (2 * c + 4) := by
  have hX0 : 0 < X := by omega
  have le : ∀ a, a ≤ 2 * c + 2 → X ^ a ≤ X ^ (2 * c + 2) := fun a ha => Nat.pow_le_pow_right hX0 ha
  have z0 : 1 ≤ X ^ (2 * c + 2) := Nat.one_le_pow _ _ hX0
  have z1 : X ≤ X ^ (2 * c + 2) := by simpa using le 1 (by omega)
  have zm : m ≤ X ^ (2 * c + 2) := hm.trans (le c (by omega))
  have zmm : m * m ≤ X ^ (2 * c + 2) := (Nat.mul_le_mul hm hm).trans (by rw [← pow_add]; exact le _ (by omega))
  have zmX : m * (2 * lam) ≤ X ^ (2 * c + 2) := (Nat.mul_le_mul hm hlam).trans (by rw [← pow_succ]; exact le _ (by omega))
  have zmR : m * R ≤ X ^ (2 * c + 2) := (Nat.mul_le_mul hm hR).trans (by rw [← pow_two, ← pow_add]; exact le _ (by omega))
  have e1 : m * (m + 1 + 1) = m * m + 2 * m := by ring
  have e2 : m * (2 * lam + 1 + 1) = m * (2 * lam) + 2 * m := by ring
  have top : 64 * X ^ (2 * c + 2) ≤ X ^ (2 * c + 4) := by
    have : X ^ (2 * c + 4) = X ^ 2 * X ^ (2 * c + 2) := by rw [← pow_add]; congr 1; omega
    rw [this]
    exact Nat.mul_le_mul_right _ (by simpa using Nat.pow_le_pow_left hX 2)
  rw [e1, e2] at hsl
  omega
end ExplicitCost
