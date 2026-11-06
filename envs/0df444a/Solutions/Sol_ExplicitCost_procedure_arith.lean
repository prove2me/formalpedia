-- Prove2me | solution 1 for ExplicitCost.procedure_arith
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:48:09.798451+00:00
-- url     : https://prove2.me/submissions/05d278ae-82db-41cb-aed7-666dcac733e1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CallFacts
import Definitions.Def_CountedRecursion_ParentSize
import Definitions.Def_CountedRecursion_Within
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_ProcedureCost
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
theorem _root_.solution {X A C₂ c₁ e s G sp : ℕ} (hX : 2 ≤ X) (hA : 2 ≤ A) (hG : G ≤ X ^ e) (hsp : sp ≤ X ^ s) :
    (A * X ^ C₂ + 2) * G ^ c₁ ≤ A * X ^ (C₂ + e * c₁ + s + 2) ∧ sp + G ^ c₁ + X ^ C₂ + 1 ≤ X ^ (C₂ + e * c₁ + s + 2) := by
  have hX0 : 0 < X := by omega
  have hv : G ^ c₁ ≤ X ^ (e * c₁) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left hG c₁
  have etop : X ^ (C₂ + e * c₁ + s + 2) = X ^ C₂ * X ^ (e * c₁) * X ^ s * X ^ 2 := by rw [pow_add, pow_add, pow_add]
  have h4 : 4 ≤ X ^ 2 := by simpa using Nat.pow_le_pow_left hX 2
  have hu1 : 1 ≤ X ^ C₂ := Nat.one_le_pow _ _ hX0
  have hv1 : 1 ≤ X ^ (e * c₁) := Nat.one_le_pow _ _ hX0
  have hw1 : 1 ≤ X ^ s := Nat.one_le_pow _ _ hX0
  rw [etop]
  generalize X ^ C₂ = u at *
  generalize X ^ (e * c₁) = v at *
  generalize X ^ s = w at *
  generalize X ^ 2 = r at *
  generalize G ^ c₁ = k at *
  have t4 : u * v * w * 4 ≤ u * v * w * r := Nat.mul_le_mul_left _ h4
  have tu : u * 1 * 1 ≤ u * v * w := Nat.mul_le_mul (Nat.mul_le_mul le_rfl hv1) hw1
  have tv : 1 * v * 1 ≤ u * v * w := Nat.mul_le_mul (Nat.mul_le_mul hu1 le_rfl) hw1
  have tw : 1 * 1 * w ≤ u * v * w := Nat.mul_le_mul (Nat.mul_le_mul hu1 hv1) le_rfl
  have tuv : u * v * 1 ≤ u * v * w := Nat.mul_le_mul le_rfl hw1
  constructor
  · have h2 : 2 ≤ A * u := hA.trans (Nat.le_mul_of_pos_right _ hu1)
    calc (A * u + 2) * k ≤ (A * u + A * u) * v := Nat.mul_le_mul (by omega) hv
      _ = A * (u * v * 1 * 2) := by ring
      _ ≤ A * (u * v * w * r) := Nat.mul_le_mul_left _ (by omega)
  · omega
end ExplicitCost
