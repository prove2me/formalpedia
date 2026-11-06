-- Prove2me | solution 1 for ExplicitCost.pattern_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:04:57.670634+00:00
-- url     : https://prove2.me/submissions/4ed7d5eb-0fd8-4a6e-b863-a9cc5e5e3882

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverPattern
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverCall
import Theorems.Thm_ExplicitCost_child_eq
import Theorems.Thm_ExplicitCost_child_size
import Theorems.Thm_ClauseBound_Alg_Level_abs_value_le
import Theorems.Thm_ClauseBound_Gen_Pick_K_le_g
import Theorems.Thm_ExplicitCost_K_le_g
import Theorems.Thm_ExplicitCost_Net_abs_value_le
import Theorems.Thm_ExplicitCost_child_value
import Theorems.Thm_ExplicitCost_length_unary
import Theorems.Thm_ExplicitCost_nParts_self
import Theorems.Thm_ExplicitCost_nPatterns_ready
import Theorems.Thm_ExplicitCost_patternValue_within
import Theorems.Thm_ExplicitCost_pattern_input
import Theorems.Thm_ExplicitCost_rG_ready
import Theorems.Thm_ExplicitCost_rK_ready
import Theorems.Thm_ExplicitCost_size_le_of_le
import Theorems.Thm_ExplicitCost_two_le_K
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Prog_abs_value_le
import Theorems.Thm_Groundwork_RebalanceArith_size_le
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
import Theorems.Thm_P2M_ExplicitCost_size_unary__02a080207638
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_Printed_AchievedBy_mono
import Theorems.Thm_Printed_asked_isNetworkP
import Theorems.Thm_Printed_length_unary
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
variable {ρ : ℝ} {c x₀ l y : ℕ} {D : PiecesCounted.Data} {a : Ctx} {f : TableQuery → Option Ans}
namespace ExplicitCost
theorem _root_.solution (hGW : GroupingWithCall) (hLL : LabelLengthIsL) (hV : ValueIsKept) (hBN : BothNetworks) (hC2 : CaseTwoApplies) (hSub : QueryMachines.StSubstWithin) (c : ℕ) :
    ∃ Cg : ℕ, ∀ (ρ : ℝ) (x₀ : ℕ) (D : PiecesCounted.Data), Setting ρ c x₀ D → ∀ (Bound : Ctx → Prop) (a : Ctx) (f : TableQuery → Option Ans) (l : ℕ), Fits x₀ a f → cLev a = l + 1 → ∀ y < nPatterns (readyOf D x₀ a.1),
      (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)).value.natAbs ≤ 2 ^ (Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a) + Levels.Gen.g x₀ l * Levels.Gen.g x₀ l * (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))) ∧
      ∀ tc tq Lam : ℕ, (patternValue c).Within ((spec D c x₀ Bound).oracle (piecesUpTo D Lam) a f) (solPrices c tc tq) (readyOf D x₀ a.1, y) (Cg * Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l + (tc + 2))
        ((Levels.Gen.g x₀ l * ((Levels.Gen.g x₀ l ^ 3 * cLam a) + (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))) + size ((1 : ℕ), 2 ^ (l + 5))) ^ Cg + (Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a) + Levels.Gen.g x₀ l * Levels.Gen.g x₀ l * (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))) + 2 * (2 * size (readyOf D x₀ a.1) + 2 * size (nPatterns (readyOf D x₀ a.1)) + size (Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l) + 2 * Levels.Gen.g x₀ l + 6 * (Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a)) + 2 * bitsOut (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)) + 12)) (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)).value := by
  obtain ⟨Cg, hCg⟩ := hGW
  refine ⟨Cg, fun ρ x₀ D hS Bound a f l hF hl y hy => ?_⟩
  obtain ⟨hIs, hsi, hL, hL3⟩ := pattern_input hLL hBN hS hF hl hy
  have hK2 := two_le_K (by have := hS.x₀_ge; omega : 1 ≤ x₀) l
  have hKg := K_le_g x₀ l
  have hK0 : 0 < Levels.Gen.K x₀ l := by omega
  have habs : (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)).value.natAbs ≤ 2 ^ (Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a) + Levels.Gen.g x₀ l * Levels.Gen.g x₀ l * (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))) := by
    have h1 := Net.abs_value_le _ hIs
    have e : nParts (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) * (Levels.Gen.g x₀ l ^ 3 * cLam a) + nParts (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) * nParts (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) * (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)) = Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a) + Levels.Gen.g x₀ l * Levels.Gen.g x₀ l * (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)) := by rw [nParts_self]
    rw [e, ← Int.natCast_natAbs] at h1
    exact_mod_cast h1
  refine ⟨habs, fun tc tq Lam => ?_⟩
  have hy' := hy
  rw [nPatterns_ready D x₀ a.1 hl] at hy'
  have hcase := hC2 ρ c x₀ D hS l (cLam a) y (direction (readyOf D x₀ a.1, y)) (readTables f) hF.1 hy'
  obtain ⟨x, hx, hfind, -, hY, hrun⟩ := hCg 1 (2 ^ (l + 5)) (Levels.Gen.K x₀ l) _ hK0 (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)) (tc + 2) hK2 (by rw [nParts_self]; omega) one_pos Nat.one_le_two_pow hIs (by rw [Nat.cast_one]; exact hcase)
  have e : Levels.Gen.K x₀ l ^ nParts (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) = Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l := by rw [nParts_self]
  have e' : nParts (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) * ((Levels.Gen.g x₀ l ^ 3 * cLam a) + (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))) = Levels.Gen.g x₀ l * ((Levels.Gen.g x₀ l ^ 3 * cLam a) + (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))) := by rw [nParts_self]
  rw [e] at hx hfind hrun
  rw [e'] at hrun
  have hval : (Value.groupClique asked.under (netInput (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))) (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)) hK0 x (AppRunningTime.Lof (Levels.Gen.K x₀ l) (nParts (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y))) (((1 : ℕ) : ℝ) / ((2 ^ (l + 5) : ℕ) : ℝ)) (Levels.Gen.g x₀ l ^ 3 * cLam a) (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)).U)).value = (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)).value :=
    hV NetInput _ (Levels.Gen.K x₀ l) hK0 (asked.close (netOracle (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)))) (netInput (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))) (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)) 1 _ (asked_isNetworkP (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)) hIs) x _ hY
  have hce := child_eq hLL hBN hS hF hl hy x
  have hChild : (spec D c x₀ Bound).Child a f (child ((readyOf D x₀ a.1, y), callOf (searchInput c (readyOf D x₀ a.1, y), x))) :=
    ⟨by rw [hl]; omega, y, x, hy, by rw [rK_ready D x₀ a.1 hl, rG_ready D x₀ a.1 hl, hsi]; exact hfind, rfl⟩
  have hO : (spec D c x₀ Bound).oracle (piecesUpTo D Lam) a f (Sum.inl (child ((readyOf D x₀ a.1, y), callOf (searchInput c (readyOf D x₀ a.1, y), x)))) = some (.inl (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)).value) := by
    have h1 : (spec D c x₀ Bound).oracle (piecesUpTo D Lam) a f (Sum.inl (child ((readyOf D x₀ a.1, y), callOf (searchInput c (readyOf D x₀ a.1, y), x)))) =
        some ((spec D c x₀ Bound).val (child ((readyOf D x₀ a.1, y), callOf (searchInput c (readyOf D x₀ a.1, y), x))) ((spec D c x₀ Bound).tab (child ((readyOf D x₀ a.1, y), callOf (searchInput c (readyOf D x₀ a.1, y), x))) f)) := by
      unfold Tower.Spec.oracle
      exact if_pos hChild
    rw [h1, child_value D c x₀ Bound _ f (K := Levels.Gen.K x₀ l) (g := Levels.Gen.g x₀ l) (lam := cLam a) (B := cB a) (y := y) (x := x) (tr := direction (readyOf D x₀ a.1, y))
      (L := AppRunningTime.Lof (Levels.Gen.K x₀ l) (nParts (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y))) (((1 : ℕ) : ℝ) / ((2 ^ (l + 5) : ℕ) : ℝ)) (Levels.Gen.g x₀ l ^ 3 * cLam a) (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)).U)
      (by rw [hce]; show Levels.Gen.K x₀ (unary l).length = _; rw [length_unary]) (by rw [hce]; rfl) (by rw [hce]; show (unary _).length = _; rw [length_unary, hL]) hK0, hval]
  have hrun' := patternValue_within hSub (c := c) (w := solPrices c tc tq) (v := (readyOf D x₀ a.1, y)) (x := x) (tc := tc) (Zc := (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)).value)
    (hG := fun O' hO' => by rw [hsi] at hO' ⊢; exact hrun O' (by rw [hO', hval])) hO rfl
  refine hrun'.mono le_rfl ?_
  have s0 := child_size hLL hBN hS Bound hF hl _ hChild
  have s1 : size (Sum.inl (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)).value : Ans) ≤ Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a) + Levels.Gen.g x₀ l * Levels.Gen.g x₀ l * (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)) + 3 := by
    have h2 : (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)).value.natAbs.size ≤ Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a) + Levels.Gen.g x₀ l * Levels.Gen.g x₀ l * (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)) + 1 := Nat.size_le.2 (habs.trans_lt (Nat.pow_lt_pow_right (by norm_num) (by omega)))
    simp only [size_inl, size_int]
    omega
  have s2 := size_le_of_le hy.le
  have s3 : size (callOf (searchInput c (readyOf D x₀ a.1, y), x)) ≤ size (child ((readyOf D x₀ a.1, y), callOf (searchInput c (readyOf D x₀ a.1, y), x))) + 2 * Levels.Gen.K x₀ l := by
    have h1 : inK (searchInput c (readyOf D x₀ a.1, y)) = Levels.Gen.K x₀ l := by rw [hsi]; exact length_unary _
    have h6 : size (callOf (searchInput c (readyOf D x₀ a.1, y), x)) = size x + (size (unary (inK (searchInput c (readyOf D x₀ a.1, y)))) + (size (child ((readyOf D x₀ a.1, y), callOf (searchInput c (readyOf D x₀ a.1, y), x))).1.2.1 + size (child ((readyOf D x₀ a.1, y), callOf (searchInput c (readyOf D x₀ a.1, y), x))).1.2.2)) := rfl
    have h7 : size (child ((readyOf D x₀ a.1, y), callOf (searchInput c (readyOf D x₀ a.1, y), x))) = size (child ((readyOf D x₀ a.1, y), callOf (searchInput c (readyOf D x₀ a.1, y), x))).1.1 + (size (child ((readyOf D x₀ a.1, y), callOf (searchInput c (readyOf D x₀ a.1, y), x))).1.2.1 + size (child ((readyOf D x₀ a.1, y), callOf (searchInput c (readyOf D x₀ a.1, y), x))).1.2.2) +
        (size (parentAt (readyOf D x₀ a.1, y) x).1 + (size (parentAt (readyOf D x₀ a.1, y) x).2.1 + (size (parentAt (readyOf D x₀ a.1, y) x).2.2.1 + (1 + (size y + size x)))) + 1) := rfl
    rw [h6, h7, h1, size_unary']
    omega
  have t1 : size ((readyOf D x₀ a.1, y) : Ready × ℕ) = size (readyOf D x₀ a.1) + size y := rfl
  have t2 : size (((readyOf D x₀ a.1, y), callOf (searchInput c (readyOf D x₀ a.1, y), x)) : (Ready × ℕ) × CliqueCall) = size (readyOf D x₀ a.1) + size y + size (callOf (searchInput c (readyOf D x₀ a.1, y), x)) := rfl
  rw [t1, t2]
  omega
end ExplicitCost
