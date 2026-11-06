-- Prove2me | solution 1 for ClauseBound.Inst.Half.partH_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:55:11.893904+00:00
-- url     : https://prove2.me/submissions/6a3098b1-08b1-4692-99bd-3946d945d7c1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_ClauseBound_Inst_HalfVal
import Theorems.Thm_ClauseBound_Inst_Half_Val_pad_allTab
import Theorems.Thm_ClauseBound_Inst_Half_partT_eq
import Theorems.Thm_ClauseBound_Inst_Half_allTabF_eq
import Theorems.Thm_ClauseBound_Inst_Half_two_le_hF
import Theorems.Thm_Groundwork_PolyT_elim
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
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec Finset
open Val
namespace ClauseBound.Inst.Half
theorem _root_.solution (hT : StTopF) (hB : StBotF) {c₀ lam : ℕ} {pad : U} (hp : padLen (hF c₀ lam) ≤ pad.length) (tr top : Bool) (h' i : ℕ)
    (a b : Pieces.Bits lam) (θ : List Bool)
    (ha : encF (allTab (4 * hF c₀ lam)) (hF c₀ lam) (bitsOf a) ∈ (allTab (4 * hF c₀ lam)).flatten ∧
      (encF (allTab (4 * hF c₀ lam)) (hF c₀ lam) (bitsOf a)).sum = hF c₀ lam)
    (hb : encF (allTab (4 * hF c₀ lam)) (hF c₀ lam) (bitsOf b) ∈ (allTab (4 * hF c₀ lam)).flatten ∧
      (encF (allTab (4 * hF c₀ lam)) (hF c₀ lam) (bitsOf b)).sum = hF c₀ lam) :
    partH c₀ top ((pad, tr), (h', i), (bitsOf a, bitsOf b, θ)) =
      ((labs (allTab (4 * hF c₀ lam)) tr (hF c₀ lam) (sOf (hF c₀ lam) i))[ofWord θ]?).elim 0
        (valK tr top (hF c₀ lam) (sOf (hF c₀ lam) i) (encF (allTab (4 * hF c₀ lam)) (hF c₀ lam) (bitsOf a))
          (encF (allTab (4 * hF c₀ lam)) (hF c₀ lam) (bitsOf b))) := by
  have hl : (bitsOf a).length = lam := List.length_ofFn
  simp only [partH, hl]
  rw [allTabF_eq (pad_allTab hp)]
  exact partT_eq hT hB ((by norm_num : 1 ≤ 2).trans (two_le_hF c₀ lam)) hp tr top _ _ _ θ ha hb
end ClauseBound.Inst.Half
