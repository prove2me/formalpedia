-- Prove2me | solution 1 for ClauseBound.Inst.Half.tabOp_rep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:48:14.0239+00:00
-- url     : https://prove2.me/submissions/d09f052c-b358-4db1-b854-834759b2391f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTab
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_ClauseBound_Inst_HalfTabSpec
import Theorems.Thm_ClauseBound_Inst_Half_rep_tab
import Theorems.Thm_ClauseBound_Inst_Half_len_tab_le
import Theorems.Thm_ClauseBound_Inst_Half_nopE_eq
import Theorems.Thm_ClauseBound_Inst_Half_oneT_rep
import Theorems.Thm_ClauseBound_Inst_Half_tabOp_nil
import Theorems.Thm_ClauseBound_Inst_Half_tabOp_cons
import Theorems.Thm_ClauseBound_Inst_Half_padOp_mono
import Theorems.Thm_ClauseBound_Boson_abs_op_le
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_sum
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
import Theorems.Thm_PaddedDescent_F_cap_eq
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
namespace ClauseBound.Inst.Half
theorem _root_.solution {pad : U} {W : ℕ} {flat : List (List ℕ)} {a : List ℕ} (hW : 1 ≤ W) (hf : FlatOK W flat) (ha : ∀ n ∈ a, n ≤ W)
    (hp : padOp W flat.length a.length ≤ pad.length) : Rep flat (tabOp pad W flat a) (op a) := by
  induction a with
  | nil =>
    have hlen : len (oneT flat) ≤ pad.length := by
      refine (len_tab_le (B := 0) fun π _ σ _ => ?_).trans (by simpa [padOp] using hp)
      split_ifs <;> simp
    rw [tabOp_nil, cap_eq hlen]
    exact oneT_rep hf
  | cons n a ih =>
    have ih' := ih (fun x hx => ha x (by simp [hx])) ((padOp_mono W _ (by simp)).trans hp)
    have hE : ∀ π ∈ flat, ∀ σ ∈ flat, nopE W n flat (tabOp pad W flat a) π σ = op (n :: a) ((π.sum : ℤ) - σ.sum) π σ :=
      fun π hπ σ hσ => nopE_eq hf (ha n (by simp)) ih' hπ hσ
    have hlen : len (tab flat (nopE W n flat (tabOp pad W flat a))) ≤ pad.length := by
      refine (len_tab_le (B := (4 * W + 1) * (n :: a).length) fun π hπ σ hσ => ?_).trans hp
      rw [hE π hπ σ hσ]
      exact abs_op_le hW (n :: a) ha _ (by simpa using hf.sum_le π hπ) (by simpa using hf.sum_le σ hσ)
    rw [tabOp_cons, cap_eq hlen]
    exact rep_tab hE
end ClauseBound.Inst.Half
