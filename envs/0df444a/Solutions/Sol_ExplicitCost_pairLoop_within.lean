-- Prove2me | solution 1 for ExplicitCost.pairLoop_within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:25:14.487881+00:00
-- url     : https://prove2.me/submissions/e17d54ea-ec6b-4379-9e5a-319d1a56f44d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RowWeightRun
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_RowPairRun
import Theorems.Thm_ExplicitCost_length_rectStrings
import Theorems.Thm_ExplicitCost_pieces_value
import Theorems.Thm_ExplicitCost_abs_pairItem_lt
import Theorems.Thm_Eight_ViaGrouping_Table_natAbs_le
import Theorems.Thm_ExplicitCost_digG_ofLists
import Theorems.Thm_ExplicitCost_dig_mem
import Theorems.Thm_ExplicitCost_ite_within_false
import Theorems.Thm_ExplicitCost_ite_within_true
import Theorems.Thm_ExplicitCost_lift_within
import Theorems.Thm_ExplicitCost_mapOut_within
import Theorems.Thm_ExplicitCost_nMemb_self
import Theorems.Thm_ExplicitCost_prodRange_within
import Theorems.Thm_ExplicitCost_query_within
import Theorems.Thm_ExplicitCost_size_answer
import Theorems.Thm_ExplicitCost_size_lt_le
import Theorems.Thm_ExplicitCost_size_two_pow_pow
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_const_runs
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
import Theorems.Thm_Groundwork_Unary_const
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
import Theorems.Thm_SingleBitPieces_Level_Presents_nMemb_self
attribute [local fun_prop] Groundwork.PolyT.const
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
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ g lam y B tq Lam : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}
namespace ExplicitCost
theorem _root_.solution (hLA : ListsAgree) {p : Parent} (hG : pG p = g) (hL : pLam p = lam) (hT : pTr p = tr) (hY : pY p = y) (hLs : pLists p = listsOf D lam) (hS : Setting ρ c x₀ D) (hg : 1 ≤ g) (hlam : 1 ≤ lam) (hLam : lam ≤ Lam)
    {q : PsiQ} (ha : q.1.1 < nParts g g tr) (hb : q.1.2 < nParts g g tr) (hz : q.2.1.length = nMemb g g tr * (g * g) * lam) (hz' : q.2.2.length = nMemb g g tr * (g * g) * lam) :
    pairLoop.Within (upOracle D g lam Lam W) (upPrices c tq) (p, q) (g * g * (askCost c lam + 1)) (2 * size (p, q) + 2 * size (g * g) + (2 * lam) ^ c * (g * g) + (2 * lam) ^ c + 9)
      (if straightOK g tr lam q = true then ∏ j ∈ range (g * g), pairItem D c g tr lam y q j else 0) := by
  subst hG hL hT hY
  by_cases hc : straightOK (pG p) (pTr p) (pLam p) q = true
  · rw [if_pos hc]
    have hbody : ∀ j < pG p * pG p, (QueryMachine.ite (fun v : (Parent × PsiQ) × ℕ => decide (v.2 / pG v.1.1 < v.2 % pG v.1.1)) (askInt fun v : (Parent × PsiQ) × ℕ => (Sum.inr (rectQuestion v) : UpQuery)) (QueryMachine.const 1)).Within
        (upOracle D (pG p) (pLam p) Lam W) (upPrices c tq) ((p, q), j) (askCost c (pLam p)) (size (p, q) + size (pG p * pG p) + (2 * pLam p) ^ c + 4) (pairItem D c (pG p) (pTr p) (pLam p) (pY p) q j) := by
      intro j hj
      have s2 := size_lt_le hj
      have s3 : size ((p, q), j) = size (p, q) + size j := rfl
      have hi : j / pG p < nMemb (pG p) (pG p) (pTr p) := by rw [nMemb_self]; exact Nat.div_lt_of_lt_mul hj
      have hi' : j % pG p < nMemb (pG p) (pG p) (pTr p) := by rw [nMemb_self]; exact Nat.mod_lt _ hg
      by_cases hlt : j / pG p < j % pG p
      · obtain ⟨l1, l2, l3, l4⟩ := length_rectStrings ha hb hz hz' hi hi'
        have hidx : pieceAt p (tri q.1.1 q.1.2) (tri (j / pG p) (j % pG p)) = indexAt D (pLam p) (digG (piecesOf D c) (pG p) (pTr p) 0 (pLam p) (pY p) (tri q.1.1 q.1.2) (tri (j / pG p) (j % pG p))) := by
          unfold pieceAt
          rw [hLs, digG_ofLists hLA hS hlam]
          rfl
        have hv : upOracle D (pG p) (pLam p) Lam W (Sum.inr (rectQuestion ((p, q), j))) = some (Sum.inl (pairItem D c (pG p) (pTr p) (pLam p) (pY p) q j)) := by
          unfold pairItem
          rw [if_pos hlt]
          change piecesUpTo D Lam (p.2.1.1, .inr (.inr (.inr (.inl (pieceAt p (tri q.1.1 q.1.2) (tri (j / pG p) (j % pG p)), rectStrings (pG p) (pTr p) (pLam p) q (j / pG p) (j % pG p)))))) = _
          rw [hidx]
          exact pieces_value (dig_mem hS hlam _ _ _ _ _) l1 l2 l3 l4 hlam hLam rfl
        have hq := query_within (A := Ans) (h := fun v : (Parent × PsiQ) × ℕ => (Sum.inr (rectQuestion v) : UpQuery)) (w := upPrices c tq) (a := ((p, q), j)) hv
        refine (ite_within_true (p := fun v : (Parent × PsiQ) × ℕ => decide (v.2 / pG v.1.1 < v.2 % pG v.1.1)) (a := ((p, q), j)) (decide_eq_true hlt) (mapOut_within (g := asInt) hq)).mono le_rfl ?_
        have s1 := size_answer (abs_pairItem_lt (g := pG p) (tr := pTr p) (y := pY p) hS hlam q j)
        omega
      · have e : pairItem D c (pG p) (pTr p) (pLam p) (pY p) q j = 1 := if_neg hlt
        rw [e]
        refine (ite_within_false (p := fun v : (Parent × PsiQ) × ℕ => decide (v.2 / pG v.1.1 < v.2 % pG v.1.1)) (a := ((p, q), j)) (decide_eq_false hlt) (lift_within (Stepped.const_runs (1 : ℤ) _))).mono ?_ ?_
        · unfold askCost
          omega
        · have : size (1 : ℤ) = 2 := rfl
          omega
    have hprod := prodRange_within (N := fun x : Parent × PsiQ => pG x.1 * pG x.1) (a := (p, q)) (fun _ => askCost c (pLam p)) (pairItem D c (pG p) (pTr p) (pLam p) (pY p) q) (2 ^ (2 * pLam p) ^ c) _ Nat.one_le_two_pow hbody
      fun j _ => Table.natAbs_le (abs_pairItem_lt hS hlam q j).le
    dsimp only at hprod
    refine (ite_within_true (p := fun x : Parent × PsiQ => straightOK (pG x.1) (pTr x.1) (pLam x.1) x.2) (a := (p, q)) hc hprod).mono (le_of_eq ?_) ?_
    · rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    · have := size_two_pow_pow ((2 * pLam p) ^ c) (pG p * pG p)
      omega
  · rw [if_neg hc]
    rw [Bool.not_eq_true] at hc
    refine (ite_within_false (p := fun x : Parent × PsiQ => straightOK (pG x.1) (pTr x.1) (pLam x.1) x.2) (a := (p, q)) hc (lift_within (Stepped.const_runs (0 : ℤ) _))).mono ?_ ?_
    · exact Nat.mul_pos (Nat.mul_pos hg hg) (Nat.succ_pos _)
    · have : size (0 : ℤ) = 1 := rfl
      omega
end ExplicitCost
