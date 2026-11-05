-- Prove2me | solution 1 for ClauseBound.TopN.EvalW.sum_vset_GW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:17:58.351204+00:00
-- url     : https://prove2.me/submissions/cbda19be-87a8-4acb-a999-3ff96c1fc0f0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_PaddedDescent_F_MarkProf
import Definitions.Def_PaddedDescent_F_MarkPi
import Definitions.Def_PaddedDescent_F_MarkPi
import Definitions.Def_ClauseBound_TopN_EvalW
import Theorems.Thm_ClauseBound_TopN_EvalW_prod_map_range
import Theorems.Thm_ClauseBound_TopN_EvalW_sum_powerset_Icc
import Theorems.Thm_ClauseBound_TopN_EvalW_GW_mul_sgnP
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
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
import Theorems.Thm_PaddedDescent_F_Mark_Pi_card_layP_vset
import Theorems.Thm_PaddedDescent_F_Mark_Pi_layer_lt
import Theorems.Thm_PaddedDescent_F_Mark_Pi_sum_powerset_layers
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
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



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.TopN ClauseBound.TopN.EvalW
open Groundwork Groundwork.Prog Finset PaddedDescent.F PaddedDescent.F.Mark
namespace ClauseBound.TopN.EvalW
theorem _root_.solution (σ : ℕ → Bool) (w : ℕ) (ws : List ℤ) (lo hi : List ℕ) (Ls : List Fml) (hw : ∀ i < Ls.length, hi.getD i 0 ≤ w) :
    (∑ P ∈ (vset σ Ls).powerset,
      if ∀ i < Ls.length, (layP Ls P i).card ≤ w then GW Ls.length ws lo hi (fun i => (layP Ls P i).card) * sgnP Ls P else 0) =
      ((List.range Ls.length).map fun i =>
        ∑ j ∈ Finset.Icc (lo.getD i 0) (hi.getD i 0), ws.getD i 0 ^ j * ((nvio σ (Ls.getD i [])).choose j : ℤ)).prod := by
  rw [prod_map_range]
  have h1 := Pi.sum_powerset_layers (fun e => (clAt Ls e).1)
    (fun i P => if lo.getD i 0 ≤ P.card ∧ P.card ≤ hi.getD i 0 then ws.getD i 0 ^ P.card else 0) Ls.length (vset σ Ls)
    fun e he => Pi.layer_lt Ls (mem_range.1 (mem_filter.1 he).1)
  have h2 : ∀ i ∈ range Ls.length, (∑ P ∈ ((vset σ Ls).filter fun e => (clAt Ls e).1 = i).powerset,
      if lo.getD i 0 ≤ P.card ∧ P.card ≤ hi.getD i 0 then ws.getD i 0 ^ P.card else 0) =
      ∑ j ∈ Finset.Icc (lo.getD i 0) (hi.getD i 0), ws.getD i 0 ^ j * ((nvio σ (Ls.getD i [])).choose j : ℤ) := by
    intro i _
    rw [sum_powerset_Icc, ← Pi.card_layP_vset σ Ls i]
    rfl
  rw [← prod_congr rfl h2, ← h1]
  refine sum_congr rfl fun P hPm => ?_
  have hsub : P ⊆ Finset.range (cls Ls).length := (Finset.mem_powerset.1 hPm).trans (Finset.filter_subset _ _)
  have h3 := GW_mul_sgnP ws lo hi Ls hsub
  by_cases hc : ∀ i < Ls.length, (layP Ls P i).card ≤ w
  · rw [if_pos hc, h3]
    rfl
  · rw [if_neg hc]
    simp only [not_forall] at hc
    obtain ⟨i, hi', hlt⟩ := hc
    refine (prod_eq_zero (mem_range.2 hi') (if_neg fun h => hlt (h.2.trans (hw i hi')))).symm
end ClauseBound.TopN.EvalW
