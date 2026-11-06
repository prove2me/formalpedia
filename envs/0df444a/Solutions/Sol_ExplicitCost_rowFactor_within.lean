-- Prove2me | solution 1 for ExplicitCost.rowFactor_within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:25:46.684202+00:00
-- url     : https://prove2.me/submissions/a5d6a42a-abdb-4ed5-bd04-36974015952f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RowPairRun
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_RowFactorRun
import Theorems.Thm_ExplicitCost_pieces_factor
import Theorems.Thm_ExplicitCost_length_factorChunk
import Theorems.Thm_ExplicitCost_abs_factorItem_lt
import Theorems.Thm_ExplicitCost_gridFf_items
import Theorems.Thm_ClauseBound_Alg_GridNet_length_heG
import Theorems.Thm_ClauseBound_Alg_GridNet_nodeG_lt
import Theorems.Thm_Eight_ViaGrouping_Table_natAbs_le
import Theorems.Thm_ExplicitCost_digG_ofLists
import Theorems.Thm_ExplicitCost_dig_mem
import Theorems.Thm_ExplicitCost_factor_eq
import Theorems.Thm_ExplicitCost_ite_within_false
import Theorems.Thm_ExplicitCost_ite_within_true
import Theorems.Thm_ExplicitCost_lenG_ofLists
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
    {a b : Fin (nParts g g tr)} (hab : a ≠ b) {z θ : List Bool} (hz : z.length = nMemb g g tr * (g * g) * lam) (hθ : θ.length = capG (piecesOf D c) g g tr 0 lam y a b) :
    rowFactor.Within (upOracle D g lam Lam W) (upPrices c tq) (p, ((a.val, b.val), (z, θ))) (g * g * (askCost c lam + 1))
      (2 * size (p, ((a.val, b.val), (z, θ))) + 2 * size (g * g) + (2 * lam) ^ c * (g * g) + (2 * lam) ^ c + 9) ((patternNet D c g tr lam y W).f a b z θ) := by
  rw [factor_eq hab hz hθ, gridFf_items (q := ((a.val, b.val), (z, θ))) hg b.2 hz hθ]
  subst hG hL hT hY
  obtain ⟨q, hq⟩ : ∃ q : FQ, q = ((a.val, b.val), (z, θ)) := ⟨_, rfl⟩
  have hb : q.1.2 < nParts (pG p) (pG p) (pTr p) := by rw [hq]; exact b.2
  have hz' : q.2.1.length = nMemb (pG p) (pG p) (pTr p) * (pG p * pG p) * pLam p := by rw [hq]; exact hz
  have hθ' : q.2.2.length = capG (piecesOf D c) (pG p) (pG p) (pTr p) 0 (pLam p) (pY p) q.1.1 q.1.2 := by rw [hq]; exact hθ
  rw [← hq]
  by_cases hc : labelOK (pG p) (pTr p) (pLam p) q = true
  · rw [if_pos hc]
    have hbody : ∀ j < pG p * pG p, (QueryMachine.ite (fun v : (Parent × FQ) × ℕ => decide (v.2 / pG v.1.1 < v.2 % pG v.1.1)) (askInt fun v : (Parent × FQ) × ℕ => (Sum.inr (factorQuestion v) : UpQuery)) (QueryMachine.const 1)).Within
        (upOracle D (pG p) (pLam p) Lam W) (upPrices c tq) ((p, q), j) (askCost c (pLam p)) (size (p, q) + size (pG p * pG p) + (2 * pLam p) ^ c + 4) (factorItem D c (pG p) (pTr p) (pLam p) (pY p) q j) := by
      intro j hj
      have s2 := size_lt_le hj
      have s3 : size ((p, q), j) = size (p, q) + size j := rfl
      have hi : j / pG p < nMemb (pG p) (pG p) (pTr p) := by rw [nMemb_self]; exact Nat.div_lt_of_lt_mul hj
      have hi' : j % pG p < nMemb (pG p) (pG p) (pTr p) := by rw [nMemb_self]; exact Nat.mod_lt _ hg
      by_cases hlt : j / pG p < j % pG p
      · have l1 : (heG (pG p) (pG p) (pLam p) q.2.1 (j / pG p) (nodeG (pG p) (pTr p) q.1.2 (j % pG p))).length = pLam p := length_heG hz' hi (nodeG_lt _ hb hi')
        have l2 : (heG (pG p) (pG p) (pLam p) q.2.1 (j % pG p) (nodeG (pG p) (pTr p) q.1.2 (j / pG p))).length = pLam p := length_heG hz' hi' (nodeG_lt _ hb hi)
        have l3 := length_factorChunk hθ' hlt hg
        have hidx : pieceAt p (tri (min q.1.1 q.1.2) (max q.1.1 q.1.2)) (tri (j / pG p) (j % pG p)) = indexAt D (pLam p) (factorDigit D c (pG p) (pTr p) (pLam p) (pY p) q j) := by
          unfold pieceAt factorDigit
          rw [hLs, digG_ofLists hLA hS hlam]
          rfl
        have hlen : lenG (listsAsPieces (pLists p)) (pG p) (pTr p) 0 (pLam p) (pY p) (tri (min q.1.1 q.1.2) (max q.1.1 q.1.2)) = lenG (piecesOf D c) (pG p) (pTr p) 0 (pLam p) (pY p) (tri (min q.1.1 q.1.2) (max q.1.1 q.1.2)) := by
          funext κ
          rw [hLs, lenG_ofLists hLA hS hlam]
        have hv : upOracle D (pG p) (pLam p) Lam W (Sum.inr (factorQuestion ((p, q), j))) = some (Sum.inl (factorItem D c (pG p) (pTr p) (pLam p) (pY p) q j)) := by
          unfold factorItem
          rw [if_pos hlt]
          change piecesUpTo D Lam (p.2.1.1, .inr (.inr (.inr (.inr ((pTr p, !decide (q.1.1 < q.1.2)), pieceAt p (tri (min q.1.1 q.1.2) (max q.1.1 q.1.2)) (tri (j / pG p) (j % pG p)),
            (heG (pG p) (pG p) (pLam p) q.2.1 (j / pG p) (nodeG (pG p) (pTr p) q.1.2 (j % pG p)), heG (pG p) (pG p) (pLam p) q.2.1 (j % pG p) (nodeG (pG p) (pTr p) q.1.2 (j / pG p)),
              chunkAt (lenG (listsAsPieces (pLists p)) (pG p) (pTr p) 0 (pLam p) (pY p) (tri (min q.1.1 q.1.2) (max q.1.1 q.1.2))) (tri (j / pG p) (j % pG p)) (q.2.2.drop (pG p * pLam p)))))))) = _
          rw [hidx, hlen]
          exact pieces_factor (dig_mem hS hlam _ _ _ _ _) _ _ l1 l2 l3 hlam hLam rfl
        have hq' := query_within (A := Ans) (h := fun v : (Parent × FQ) × ℕ => (Sum.inr (factorQuestion v) : UpQuery)) (w := upPrices c tq) (a := ((p, q), j)) hv
        refine (ite_within_true (p := fun v : (Parent × FQ) × ℕ => decide (v.2 / pG v.1.1 < v.2 % pG v.1.1)) (a := ((p, q), j)) (decide_eq_true hlt) (mapOut_within (g := asInt) hq')).mono le_rfl ?_
        have s1 := size_answer (abs_factorItem_lt hS hlam hg hθ' j)
        omega
      · have e : factorItem D c (pG p) (pTr p) (pLam p) (pY p) q j = 1 := if_neg hlt
        rw [e]
        refine (ite_within_false (p := fun v : (Parent × FQ) × ℕ => decide (v.2 / pG v.1.1 < v.2 % pG v.1.1)) (a := ((p, q), j)) (decide_eq_false hlt) (lift_within (Stepped.const_runs (1 : ℤ) _))).mono ?_ ?_
        · unfold askCost
          omega
        · have : size (1 : ℤ) = 2 := rfl
          omega
    have hprod := prodRange_within (N := fun x : Parent × FQ => pG x.1 * pG x.1) (a := (p, q)) (fun _ => askCost c (pLam p)) (factorItem D c (pG p) (pTr p) (pLam p) (pY p) q) (2 ^ (2 * pLam p) ^ c) _ Nat.one_le_two_pow hbody
      fun j _ => Table.natAbs_le (abs_factorItem_lt hS hlam hg hθ' j).le
    dsimp only at hprod
    refine (ite_within_true (p := fun x : Parent × FQ => labelOK (pG x.1) (pTr x.1) (pLam x.1) x.2) (a := (p, q)) hc hprod).mono (le_of_eq ?_) ?_
    · rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    · have := size_two_pow_pow ((2 * pLam p) ^ c) (pG p * pG p)
      omega
  · rw [if_neg hc]
    rw [Bool.not_eq_true] at hc
    refine (ite_within_false (p := fun x : Parent × FQ => labelOK (pG x.1) (pTr x.1) (pLam x.1) x.2) (a := (p, q)) hc (lift_within (Stepped.const_runs (0 : ℤ) _))).mono ?_ ?_
    · exact Nat.mul_pos (Nat.mul_pos hg hg) (Nat.succ_pos _)
    · have : size (0 : ℤ) = 1 := rfl
      omega
end ExplicitCost
