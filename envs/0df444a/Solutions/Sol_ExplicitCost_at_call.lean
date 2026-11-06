-- Prove2me | solution 1 for ExplicitCost.at_call
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:40:06.599101+00:00
-- url     : https://prove2.me/submissions/e8af1ba7-7f4d-484c-b2ab-f5a5e9d95681

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CallLemma
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CallFacts
import Theorems.Thm_ExplicitCost_Lof_bounds
import Theorems.Thm_ExplicitCost_firstGrouping_cast
import Theorems.Thm_ExplicitCost_fits_succ
import Theorems.Thm_ExplicitCost_length_unary
import Theorems.Thm_ExplicitCost_level_numbers
import Theorems.Thm_ExplicitCost_nParts_self
import Theorems.Thm_ExplicitCost_nPatterns_readyOf
import Theorems.Thm_ExplicitCost_netTotal_le
import Theorems.Thm_ExplicitCost_parentAt_readyOf
import Theorems.Thm_ExplicitCost_rG_readyOf
import Theorems.Thm_ExplicitCost_rK_readyOf
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_length
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
import Theorems.Thm_Printed_length_unary
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
import Theorems.Thm_SingleBitPieces_Level_Presents_nParts_self
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
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution (hG : GroupingWithCall) (hL : LabelLengthIsL) (hC : CaseTwoApplies) (hBN : BothNetworks) {ρ : ℝ} {c x₀ : ℕ} {D : PiecesCounted.Data} (hS : Setting ρ c x₀ D) {Bound : Ctx → Prop} {a a' : Ctx}
    {f : TableQuery → Option Ans} {l : ℕ} (hF : Fits x₀ a f) (hl : cLev a = l + 1) (hc : (spec D c x₀ Bound).Child a f a') : ∃ y x : ℕ, AtCall D c x₀ l a a' f y x := by
  obtain ⟨-, y, x, hy, hfind, rfl⟩ := hc
  obtain ⟨hK2, hKg, hg2⟩ := level_numbers hS.x₀_ge l
  obtain ⟨hlam, hB1, hW, -⟩ := fits_succ hF hl
  have hl' : hLev a.1 = l + 1 := hl
  have hK0 : 0 < Levels.Gen.K x₀ l := by omega
  rw [nPatterns_readyOf D x₀ a.1 hl'] at hy
  rw [rK_readyOf D x₀ a.1 hl', rG_readyOf D x₀ a.1 hl'] at hfind
  obtain ⟨C₂, hBN⟩ := hBN c
  have hb := fun x' (hx' : x' < Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l) =>
    hBN ρ x₀ D hS (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) (cLam a) (cB a) y x' 0 (cLam a) (direction (readyOf D x₀ a.1, y)) (readTables f) hg2 hKg hlam le_rfl hB1 hW hy hx'
  obtain ⟨hIs, -, hdata0, -⟩ := hb 0 (Nat.pow_pos hK0)
  have hpar : ∀ x', parentAt (readyOf D x₀ a.1, y) x' = callParent D x₀ l a y x' := fun x' => parentAt_readyOf D x₀ a.1 hl' y x'
  have hin : searchInput c (readyOf D x₀ a.1, y) = ((1, 2 ^ (l + 5)), ((unary (Levels.Gen.K x₀ l), unary (Levels.Gen.g x₀ l)),
      netInput (callNet D c x₀ l a f y) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)))) := by
    have e : hLev (rHead (readyOf D x₀ a.1, y).1) + 4 = l + 5 := by
      change hLev a.1 + 4 = l + 5
      omega
    unfold searchInput
    rw [hpar, e]
    exact congrArg (Prod.mk (1, 2 ^ (l + 5))) hdata0
  rw [hin] at hfind
  obtain ⟨hx, h1, h2, h3⟩ := firstGrouping_cast hG hL (nParts_self _ _) hK0 (callNet D c x₀ l a f y) hK2 hg2 Nat.one_le_two_pow hIs
    (hC ρ c x₀ D hS l (cLam a) y (direction (readyOf D x₀ a.1, y)) (readTables f) hlam hy) hfind
  have hU : (callNet D c x₀ l a f y).U ≤ Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a) :=
    (netTotal_le _ hIs).trans_eq (by rw [nParts_self])
  obtain ⟨hL1, hL2⟩ := Lof_bounds (b := 2 ^ (l + 5)) hK2 (by omega) hIs.P_pos Nat.one_le_two_pow hU
  refine ⟨y, x, hy, hx, ?_, ?_, ?_, hpar x, hIs, (hb x hx).2.2.1, fun _ => h1, fun _ => h2, hL1, hL2⟩
  · change (a.1.1.tail).length = l
    have e : a.1.1.length = l + 1 := hl
    rw [List.length_tail, e]
    rfl
  · change (unary (labelLength (searchInput c (readyOf D x₀ a.1, y)))).length = _
    rw [length_unary, hin]
    exact h3
  · change (unary (bitsOut (inK (searchInput c (readyOf D x₀ a.1, y))) (inG (searchInput c (readyOf D x₀ a.1, y))) (inP (searchInput c (readyOf D x₀ a.1, y))) (inB (searchInput c (readyOf D x₀ a.1, y))))).length = _
    rw [length_unary, hin]
    change bitsOut (unary _).length (unary _).length (unary _).length (unary _).length = _
    simp only [length_unary]
end ExplicitCost
