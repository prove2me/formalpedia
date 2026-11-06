-- Prove2me | solution 1 for ExplicitCost.rowWeight_within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:25:13.334961+00:00
-- url     : https://prove2.me/submissions/90b0552b-c0ea-4e19-a273-2c8755f415bb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_ParentNumbers
import Definitions.Def_CountedRecursion_Within
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_RowWeightRun
import Theorems.Thm_ExplicitCost_size_answer
import Theorems.Thm_ExplicitCost_size_lt_le
import Theorems.Thm_ExplicitCost_size_two_pow_pow
import Theorems.Thm_ExplicitCost_answersOf_eq
import Theorems.Thm_Eight_ViaGrouping_Table_natAbs_le
import Theorems.Thm_ExplicitCost_ite_within_false
import Theorems.Thm_ExplicitCost_ite_within_true
import Theorems.Thm_ExplicitCost_lift_within
import Theorems.Thm_ExplicitCost_mapOut_within
import Theorems.Thm_ExplicitCost_nMemb_self
import Theorems.Thm_ExplicitCost_pointQuery_ok
import Theorems.Thm_ExplicitCost_prodRange_within
import Theorems.Thm_ExplicitCost_query_within
import Theorems.Thm_ExplicitCost_weight_eq
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
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
variable {D : PiecesCounted.Data} {c g lam y B tq Lam : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}
namespace ExplicitCost
theorem _root_.solution {p : Parent} (hG : pG p = g) (hL : pLam p = lam) (hT : pTr p = tr) (hg : 1 ≤ g) (hW : ∀ w < g * g, ∀ z ∈ words ((g * g - 1) * lam), |W w z| < 2 ^ B)
    (a : Fin (nParts g g tr)) {z : List Bool} (hz : z.length = nMemb g g tr * (g * g) * lam) :
    rowWeight.Within (upOracle D g lam Lam W) (upPrices c tq) (p, (a.val, z)) (g * (tq + 1)) (2 * size (p, (a.val, z)) + 2 * size g + B * g + B + 8) ((patternNet D c g tr lam y W).W a z) := by
  subst hG hL hT
  rw [weight_eq a hz]
  by_cases hc : chkG (pG p) (pG p) (pTr p) (pLam p) (a.val, z) = true
  · rw [if_pos hc, nMemb_self]
    have hbody : ∀ i < pG p, (askInt fun v : (Parent × WQ) × ℕ => (Sum.inl (toTable (pointQuery (pG v.1.1) (pTr v.1.1) (pLam v.1.1) v.1.2 v.2)) : UpQuery)).Within
        (upOracle D (pG p) (pLam p) Lam W) (upPrices c tq) ((p, (a.val, z)), i) tq (size (p, (a.val, z)) + size (pG p) + B + 3)
        (W (toTable (pointQuery (pG p) (pTr p) (pLam p) (a.val, z) i)).1 (toTable (pointQuery (pG p) (pTr p) (pLam p) (a.val, z) i)).2) := by
      intro i hi
      obtain ⟨q1, q2⟩ := pointQuery_ok a hz (by rw [nMemb_self]; exact hi)
      have hq := query_within (A := Ans) (h := fun v : (Parent × WQ) × ℕ => (Sum.inl (toTable (pointQuery (pG v.1.1) (pTr v.1.1) (pLam v.1.1) v.1.2 v.2)) : UpQuery))
        (O := upOracle D (pG p) (pLam p) Lam W) (w := upPrices c tq) (a := ((p, (a.val, z)), i)) (answersOf_eq q1 q2)
      dsimp only at hq
      refine (mapOut_within (g := asInt) hq).mono le_rfl ?_
      have s1 := size_answer (hW _ q1 _ (mem_words.2 q2))
      have s2 := size_lt_le hi
      have s3 : size ((p, (a.val, z)), i) = size (p, (a.val, z)) + size i := rfl
      omega
    have hprod := prodRange_within (N := fun x : Parent × WQ => pG x.1) (a := (p, (a.val, z))) (fun _ => tq)
      (fun i => W (toTable (pointQuery (pG p) (pTr p) (pLam p) (a.val, z) i)).1 (toTable (pointQuery (pG p) (pTr p) (pLam p) (a.val, z) i)).2) (2 ^ B) _ Nat.one_le_two_pow hbody
      fun i hi => by
        obtain ⟨q1, q2⟩ := pointQuery_ok a hz (by rw [nMemb_self]; exact hi)
        exact Table.natAbs_le (hW _ q1 _ (mem_words.2 q2)).le
    dsimp only at hprod
    refine (ite_within_true (p := fun x : Parent × WQ => chkG (pG x.1) (pG x.1) (pTr x.1) (pLam x.1) x.2) (a := (p, (a.val, z))) hc hprod).mono (le_of_eq ?_) ?_
    · rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    · have := size_two_pow_pow B (pG p)
      omega
  · rw [if_neg hc]
    rw [Bool.not_eq_true] at hc
    refine (ite_within_false (p := fun x : Parent × WQ => chkG (pG x.1) (pG x.1) (pTr x.1) (pLam x.1) x.2) (a := (p, (a.val, z))) hc (lift_within (Stepped.const_runs (0 : ℤ) _))).mono ?_ ?_
    · exact Nat.mul_pos hg (Nat.succ_pos _)
    · have : size (0 : ℤ) = 1 := rfl
      omega
end ExplicitCost
