-- Prove2me | solution 1 for ClauseBound.Inst.Half.topF_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:55:32.155017+00:00
-- url     : https://prove2.me/submissions/70b33528-03f6-48c9-bd67-0832b9ca74a4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTabSpec
import Definitions.Def_ClauseBound_Boson_KF
import Definitions.Def_ClauseBound_Boson_Half
import Definitions.Def_ClauseBound_Inst_HalfTabKF
import Theorems.Thm_ClauseBound_Inst_Half_tabKF_rep
import Theorems.Thm_ClauseBound_Boson_op_grade
import Theorems.Thm_ClauseBound_Boson_sum_aFam_eq
import Theorems.Thm_ClauseBound_Inst_Rec_chooseZ_eq
import Theorems.Thm_ClauseBound_Inst_Rec_sgnZ_eq
import Theorems.Thm_ClauseBound_Inst_Rec_sumR_eq
import Theorems.Thm_ClauseBound_Rec_ite_even_natCast
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_sum
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
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.sum
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
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Inst.Rec ClauseBound.Boson
open HalfTabKF
namespace ClauseBound.Inst.Half
theorem _root_.solution {pad : U} {W h : ℕ} {flat : List (List ℕ)} {μ : List ℕ} (hW : 1 ≤ W) (hf : FlatOK W flat) (hμ : ∀ n ∈ μ, n ≤ W) (hs : μ.sum = h)
    (hp : padKF W flat.length h μ.sum μ.length ≤ pad.length) (i : ℕ) (r : ℤ) {π σ : List ℕ} (hπ : π ∈ flat) (hσ : σ ∈ flat) :
    topF pad W flat h μ i r π σ = ClauseBound.Boson.topK μ h i r ↑π ↑σ := by
  unfold topF topK
  split_ifs with hr
  · rw [sum_aFam_eq μ (fun w => ((w + h).choose i : ℤ)), hs, sgnZ_eq, ClauseBound.Rec.ite_even_natCast, sumR_eq]
    congr 1
    refine sum_congr rfl fun w hw => ?_
    rw [tabKF_rep hW hf hμ hp w (Nat.lt_succ_iff.1 (mem_range.1 hw)) π hπ σ hσ, chooseZ_eq, ← Nat.cast_add, Ring.choose_natCast, hr]
  · have h0 : ∀ c : ℤ × List ℕ, op c.2 r (π : Multiset ℕ) (σ : Multiset ℕ) = 0 := fun c => by
      by_contra hne
      have := op_grade hne
      rw [Multiset.sum_coe, Multiset.sum_coe] at this
      exact hr (by omega)
    simp [h0]
end ClauseBound.Inst.Half
