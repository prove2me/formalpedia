-- Prove2me | solution 1 for ClauseBound.TopN.EvalW.evalV_weight_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:14:17.92474+00:00
-- url     : https://prove2.me/submissions/6d99797d-0949-44cb-bf43-9065e1ca4960

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_PaddedDescent_F_MarkProf
import Definitions.Def_PaddedDescent_F_MarkPi
import Definitions.Def_PaddedDescent_F_MarkPi
import Definitions.Def_ClauseBound_TopN_EvalW
import Theorems.Thm_ClauseBound_TopN_EvalW_tl_eq_card
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
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
import Theorems.Thm_PaddedDescent_F_sumF_eq
attribute [local fun_prop] Groundwork.PolyT.all
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



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.TopN ClauseBound.TopN.EvalW
open Groundwork Groundwork.Prog Finset PaddedDescent.F PaddedDescent.F.Mark
namespace ClauseBound.TopN.EvalW
theorem _root_.solution (hV : StMarkVal) (hP : StProfSum) (k : ℕ) (pad gu : U) (val : MCtx → ℤ) (nu wu βu bu : U) (Ls : List Fml) (G : (ℕ → ℕ) → ℤ)
    (hg : 0 < gu.length) (hb : 0 < bu.length) (hb' : bu.length ≤ 2 ^ βu.length) (hW : WfL k nu.length Ls)
    (hpad : nProf gu.length (cls Ls).length Ls.length ≤ pad.length)
    (hG : ∀ t t' : ℕ → ℕ, (∀ i < Ls.length, t i = t' i) → G t = G t')
    (hval : ∀ y, adm k gu.length nu.length wu.length Ls y = true → G (tl gu.length Ls y) ≠ 0 →
      val ((gu, nu, βu, bu), (Ls, y)) = (markN gu.length ((gu, nu, βu, bu), (Ls, y))).value) :
    evalV k pad gu (fun c => G (tl gu.length c.2.1 c.2.2) * val c) (nu, wu, βu, bu) Ls =
      ∑ σ : Fin nu.length → Bool, ∑ P ∈ (vset (Mark.ext σ) Ls).powerset,
        if ∀ i < Ls.length, (layP Ls P i).card ≤ wu.length then G (fun i => (layP Ls P i).card) * sgnP Ls P else 0 := by
  classical
  have h1 : ∀ y ∈ Finset.range (nProf gu.length (cls Ls).length Ls.length),
      (bif adm k gu.length nu.length wu.length Ls y then G (tl gu.length Ls y) * val ((gu, nu, βu, bu), (Ls, y)) else 0) =
        ∑ σ : Fin nu.length → Bool, ∑ P ∈ (vset (Mark.ext σ) Ls).powerset,
          (G (fun i => (layP Ls P i).card) * sgnP Ls P) *
            (if adm k gu.length nu.length wu.length Ls y = true ∧ Match gu.length nu.length Ls y P then (1 : ℤ) else 0) := by
    intro y _
    by_cases h : adm k gu.length nu.length wu.length Ls y = true
    · rw [h, cond_true]
      have h2 : G (tl gu.length Ls y) * val ((gu, nu, βu, bu), (Ls, y)) =
          G (tl gu.length Ls y) * (markN gu.length ((gu, nu, βu, bu), (Ls, y))).value := by
        by_cases h0 : G (tl gu.length Ls y) = 0
        · rw [h0, zero_mul, zero_mul]
        · rw [hval y h h0]
      rw [h2, hV k gu nu βu bu Ls y hg hb hb' hW, Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun P hPm => ?_
      have hsub : P ⊆ Finset.range (cls Ls).length := (Finset.mem_powerset.1 hPm).trans (Finset.filter_subset _ _)
      by_cases hm : Match gu.length nu.length Ls y P
      · have h3 : G (tl gu.length Ls y) = G (fun i => (layP Ls P i).card) := hG _ _ fun i hi => tl_eq_card hg hW hsub hm hi
        simp [hm, h3]
      · simp [hm]
    · have h' : adm k gu.length nu.length wu.length Ls y = false := by simpa using h
      rw [h', cond_false]
      simp
  unfold evalV
  rw [sumF_eq hpad]
  refine (Finset.sum_congr rfl h1).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun P hPm => ?_
  have hsub : P ⊆ Finset.range (cls Ls).length := (Finset.mem_powerset.1 hPm).trans (Finset.filter_subset _ _)
  have h2 := hP k gu.length nu.length wu.length Ls P hg hW hsub
  rw [← Finset.mul_sum]
  by_cases hc : ∀ i < Ls.length, (layP Ls P i).card ≤ wu.length
  · rw [if_pos hc] at h2
    rw [if_pos hc]
    have h3 : (∑ y ∈ Finset.range (nProf gu.length (cls Ls).length Ls.length),
        if adm k gu.length nu.length wu.length Ls y = true ∧ Match gu.length nu.length Ls y P then (1 : ℤ) else 0) = 1 := by
      convert h2
    rw [h3, mul_one]
  · rw [if_neg hc] at h2
    rw [if_neg hc]
    have h3 : (∑ y ∈ Finset.range (nProf gu.length (cls Ls).length Ls.length),
        if adm k gu.length nu.length wu.length Ls y = true ∧ Match gu.length nu.length Ls y P then (1 : ℤ) else 0) = 0 := by
      convert h2
    rw [h3, mul_zero]
end ClauseBound.TopN.EvalW
