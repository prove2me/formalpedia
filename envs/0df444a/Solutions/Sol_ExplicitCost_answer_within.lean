-- Prove2me | solution 1 for ExplicitCost.answer_within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:10:22.546731+00:00
-- url     : https://prove2.me/submissions/93984846-9bea-4226-8a71-08c5bfd210bd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RowFactorRun
import Definitions.Def_CountedRecursion_ParentSize
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_BothNetworks
import Theorems.Thm_ExplicitCost_cost_le
import Theorems.Thm_ExplicitCost_room_le
import Theorems.Thm_ExplicitCost_size_row_le
import Theorems.Thm_ExplicitCost_size_sq_le
import Theorems.Thm_Eight_SecNetworks_size_word
import Theorems.Thm_ExplicitCost_branch_within_inl
import Theorems.Thm_ExplicitCost_branch_within_inr
import Theorems.Thm_ExplicitCost_c_eq
import Theorems.Thm_ExplicitCost_lift_within
import Theorems.Thm_ExplicitCost_mapOut_within
import Theorems.Thm_ExplicitCost_mem_S_iff
import Theorems.Thm_ExplicitCost_nMemb_self
import Theorems.Thm_ExplicitCost_pG_mk
import Theorems.Thm_ExplicitCost_pLam_mk
import Theorems.Thm_ExplicitCost_pLists_mk
import Theorems.Thm_ExplicitCost_pTr_mk
import Theorems.Thm_ExplicitCost_pY_mk
import Theorems.Thm_ExplicitCost_pattern_c_le
import Theorems.Thm_ExplicitCost_rowFactor_within
import Theorems.Thm_ExplicitCost_rowPair_within
import Theorems.Thm_ExplicitCost_rowWeight_within
import Theorems.Thm_ExplicitCost_size_mkParent_le
import Theorems.Thm_ExplicitCost_size_nat_of_lt
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_NetE_size_word
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Prog_size_word
import Theorems.Thm_Groundwork_Sparsify_StackOK_mem
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_const_runs
import Theorems.Thm_Groundwork_Stepped_mapIn_runs
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
variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ K g lam B y x tq Lam : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}
namespace ExplicitCost
theorem _root_.solution (hPP : PairIsProduct) (hLA : ListsAgree) (hS : Setting ρ c x₀ D) (hg : 2 ≤ g) (hK : K ≤ g) (hlam : 1 ≤ lam) (hLam : lam ≤ Lam) (hB : 1 ≤ B) (hW : ∀ w < g * g, ∀ z ∈ words ((g * g - 1) * lam), |W w z| < 2 ^ B)
    (hy : y < #(D.fam lam).I ^ nRectG g g) (hx : x < K ^ g) {q : NetQuery} {v : ℤ} (hq : netOracle (patternNet D c g tr lam y W) q = some v) :
    (gridProcsData c).answer.Within (upOracle D g lam Lam W) (upPrices c tq) (mkParent D K g lam B tr y x, q) ((askCost c lam + tq) * Xi g lam B ^ (2 * c + 6)) (Xi g lam B ^ (2 * c + 6)) v := by
  have hsp := size_mkParent_le hS tr hK hg hlam hB hy hx
  have hm := nMemb_self g tr
  have hgg := size_sq_le g
  have hsg : size g ≤ g + 1 := size_nat_of_lt Nat.lt_two_pow_self
  have hgle : g ≤ g * g := Nat.le_mul_of_pos_left _ (by omega)
  rcases q with q | q | q | q
  · -- is z ∈ S_a?
    simp only [netOracle] at hq
    split_ifs at hq with h1 h2 h3
    swap
    · refine absurd ((mem_S_iff _ _).2 ?_) h3
      rw [h2, hm]
      change g ^ 3 * lam = _
      ring
    rw [← Option.some.inj hq]
    have r0 : (Stepped.mapIn (fun _ : Parent × WQ => ()) (Stepped.const true)).Runs (mkParent D K g lam B tr y x, q) 1 (max (size ()) (size true) + 1) true :=
      Stepped.mapIn_runs (f := fun _ : Parent × WQ => ()) (Stepped.const_runs true ())
    have r : (QueryMachine.mapOut (gridProcsData c).mem fun b => if b = true then (1 : ℤ) else 0).Within (upOracle D g lam Lam W) (upPrices c tq) (mkParent D K g lam B tr y x, q) 1 (max (size ()) (size true) + 1) 1 :=
      mapOut_within (g := fun b : Bool => if b = true then (1 : ℤ) else 0) (lift_within r0)
    refine (branch_within_inl (sel := dist) rfl r).mono (cost_le hg hlam hB (Or.inr (Or.inr le_rfl))) (room_le (sp := 0) (sQ := 0) hg hlam hB (Nat.zero_le _) (Nat.zero_le _) ?_)
    simp only [size_unit, size_bool]
    omega
  · -- W_a(z)
    simp only [netOracle] at hq
    split_ifs at hq with h1 h2
    rw [← Option.some.inj hq]
    have hz := (mem_S_iff _ _).1 h2
    have r := rowWeight_within (D := D) (c := c) (y := y) (tq := tq) (Lam := Lam) (p := mkParent D K g lam B tr y x) pG_mk pLam_mk pTr_mk (by omega) hW ⟨q.1, h1⟩ hz
    refine (branch_within_inr (sel := dist) rfl (branch_within_inl (sel := dist) rfl r)).mono (cost_le hg hlam hB (Or.inr (Or.inl le_rfl)))
      (room_le (sp := size (mkParent D K g lam B tr y x)) (sQ := size q) hg hlam hB hsp ?_ ?_)
    · have s1 : size q.1 ≤ g + 1 := size_row_le (⟨q.1, h1⟩ : Fin (nParts g g tr))
      have s2 := Eight.SecNetworks.size_word q.2
      rw [hz, hm] at s2
      have e : size q = size q.1 + size q.2 := rfl
      omega
    · have e : size (mkParent D K g lam B tr y x, ((⟨q.1, h1⟩ : Fin (nParts g g tr)).val, q.2)) = size (mkParent D K g lam B tr y x) + size q := rfl
      omega
  · -- Ψ_{a,b}(z, z')
    simp only [netOracle] at hq
    split_ifs at hq with h1 h2
    rw [← Option.some.inj hq]
    have hab : (⟨q.1.1, h1.1⟩ : Fin (nParts g g tr)) ≠ ⟨q.1.2, h1.2⟩ := fun e => h2.1 (congrArg Fin.val e)
    have r := rowPair_within hPP hLA (W := W) (tq := tq) (p := mkParent D K g lam B tr y x) pG_mk pLam_mk pTr_mk pY_mk pLists_mk hS hg hlam hLam hy hab h2.2.1 h2.2.2
    refine (branch_within_inr (sel := dist) rfl (branch_within_inr (sel := dist) rfl (branch_within_inl (sel := dist) rfl r))).mono (cost_le hg hlam hB (Or.inl le_rfl))
      (room_le (sp := size (mkParent D K g lam B tr y x)) (sQ := size q) hg hlam hB hsp ?_ ?_)
    · have s1 : size q.1.1 ≤ g + 1 := size_row_le (⟨q.1.1, h1.1⟩ : Fin (nParts g g tr))
      have s1' : size q.1.2 ≤ g + 1 := size_row_le (⟨q.1.2, h1.2⟩ : Fin (nParts g g tr))
      have s2 := Eight.SecNetworks.size_word q.2.1
      have s2' := Eight.SecNetworks.size_word q.2.2
      rw [(mem_S_iff _ _).1 h2.2.1, hm] at s2
      rw [(mem_S_iff _ _).1 h2.2.2, hm] at s2'
      have e : size q = (size q.1.1 + size q.1.2) + (size q.2.1 + size q.2.2) := rfl
      omega
    · have e : size (mkParent D K g lam B tr y x, (((⟨q.1.1, h1.1⟩ : Fin (nParts g g tr)).val, (⟨q.1.2, h1.2⟩ : Fin (nParts g g tr)).val), (q.2.1, q.2.2))) = size (mkParent D K g lam B tr y x) + size q := rfl
      omega
  · -- f_{a,b}(z, θ)
    simp only [netOracle] at hq
    split_ifs at hq with h1 h2
    rw [← Option.some.inj hq]
    have hab : (⟨q.1.1, h1.1⟩ : Fin (nParts g g tr)) ≠ ⟨q.1.2, h1.2⟩ := fun e => h2.1 (congrArg Fin.val e)
    have hz := (mem_S_iff _ _).1 h2.2.1
    have hθ : q.2.2.length = capG (piecesOf D c) g g tr 0 lam y q.1.1 q.1.2 := (mem_words.1 h2.2.2).trans (c_eq hab)
    have r := rowFactor_within hLA (W := W) (tq := tq) (p := mkParent D K g lam B tr y x) pG_mk pLam_mk pTr_mk pY_mk pLists_mk hS (by omega) hlam hLam hab hz hθ
    refine (branch_within_inr (sel := dist) rfl (branch_within_inr (sel := dist) rfl (branch_within_inr (sel := dist) rfl r))).mono (cost_le hg hlam hB (Or.inl le_rfl))
      (room_le (sp := size (mkParent D K g lam B tr y x)) (sQ := size q) hg hlam hB hsp ?_ ?_)
    · have s1 : size q.1.1 ≤ g + 1 := size_row_le (⟨q.1.1, h1.1⟩ : Fin (nParts g g tr))
      have s1' : size q.1.2 ≤ g + 1 := size_row_le (⟨q.1.2, h1.2⟩ : Fin (nParts g g tr))
      have s2 := Eight.SecNetworks.size_word q.2.1
      have s2' := Eight.SecNetworks.size_word q.2.2
      have hc := pattern_c_le (y := y) (W := W) hS hlam (⟨q.1.1, h1.1⟩ : Fin (nParts g g tr)) ⟨q.1.2, h1.2⟩
      rw [hz, hm] at s2
      rw [mem_words.1 h2.2.2] at s2'
      have h3 : g ^ 2 * lam ≤ g * (g * g) * lam := by
        calc g ^ 2 * lam = 1 * (g * g) * lam := by ring
          _ ≤ g * (g * g) * lam := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
      have e : size q = (size q.1.1 + size q.1.2) + (size q.2.1 + size q.2.2) := rfl
      omega
    · have e : size (mkParent D K g lam B tr y x, (((⟨q.1.1, h1.1⟩ : Fin (nParts g g tr)).val, (⟨q.1.2, h1.2⟩ : Fin (nParts g g tr)).val), (q.2.1, q.2.2))) = size (mkParent D K g lam B tr y x) + size q := rfl
      omega
end ExplicitCost
