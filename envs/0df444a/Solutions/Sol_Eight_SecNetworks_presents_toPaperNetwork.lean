-- Prove2me | solution 1 for Eight.SecNetworks.presents_toPaperNetwork
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:34:23.272197+00:00
-- url     : https://prove2.me/submissions/f70907a4-ca0f-410e-9053-5836ca35bcd5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecNetworks_Defs
import Definitions.Def_SingleBitPieces_SecNetworks_LemGrouping
import Definitions.Def_ToTuring_Poly_Comb
import Mathlib.Tactic
import Definitions.Def_Eight_SecNetworks_LemGrouping
import Theorems.Thm_Eight_SecNetworks_gated_runs
import Theorems.Thm_Eight_SecNetworks_size_bits
import Theorems.Thm_Eight_SecNetworks_Net_lab_toPaperNetwork
import Theorems.Thm_Eight_SecNetworks_Net_c_le
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
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
open Eight Eight.SecNetworks
open Groundwork Groundwork.Prog Finset Stepped
namespace Eight.SecNetworks
theorem _root_.solution {C : Type} [HasSize C] {Np : Procs C} {c : C} {g : ℕ} {N : Net g} {P B τ S : ℕ} (h : IsNetwork Np c N P B τ S) :
    Np.toPaperNetwork.Presents c N.toPaperNetwork (2 * τ + 1) (S + (size c + 2 * size g + 4 * P + 6)) where
  S_eq a := by
    change words (N.len a) = words (Np.len c a)
    rw [h.given.len_eq]
  c_eq a b hab := (h.given.cap_eq a b hab).symm
  lab_eq a b hab := by
    rw [Net.lab_toPaperNetwork h.is]
    change _ = words (Np.cap c a b)
    rw [h.given.cap_eq a b hab]
  W_runs a z hz := by
    have hz' : z.length = N.len a := hz.trans (h.given.len_eq a)
    have hrun := gated_runs h.τ_pos (h.given.mem_runs a z hz') (v := N.W a z) fun hb => h.given.W_runs a z (of_decide_eq_true hb)
    have hv : (if decide (z ∈ N.S a) = true then N.W a z else 0) = N.toPaperNetwork.W a z := by
      simp only [Net.toPaperNetwork, decide_eq_true_eq]
    rw [hv] at hrun
    refine hrun.mono le_rfl ?_
    have h1 : size a.val ≤ size g := by
      simp only [size_nat]
      exact Nat.succ_le_succ (Nat.size_le_size a.2.le)
    have h2 := h.is.len_le a
    simp only [size_prod, size_bits, hz']
    omega
  f_runs a b z θ hab hz hθ := by
    have hz' : z.length = N.len a := hz.trans (h.given.len_eq a)
    have hθ' : θ.length = N.c a b := hθ.trans (h.given.cap_eq a b hab)
    have hrun := gated_runs (M := mapIn memOfF Np.mem) (a := (c, ((a.val, b.val), (z, θ)))) h.τ_pos (mapIn_runs (h.given.mem_runs a z hz'))
      (v := N.f a b z θ) fun hb => h.given.f_runs a b hab z (of_decide_eq_true hb) θ (mem_words.2 hθ')
    have hv : (if decide (z ∈ N.S a) = true then N.f a b z θ else 0) = N.toPaperNetwork.f a b z θ := by
      simp only [Net.toPaperNetwork, decide_eq_true_eq, mem_words, hθ', hab, ne_eq, not_false_eq_true, true_and, and_true]
    rw [hv] at hrun
    refine hrun.mono le_rfl ?_
    have h1 : size a.val ≤ size g := by
      simp only [size_nat]
      exact Nat.succ_le_succ (Nat.size_le_size a.2.le)
    have h1' : size b.val ≤ size g := by
      simp only [size_nat]
      exact Nat.succ_le_succ (Nat.size_le_size b.2.le)
    have h2 := h.is.len_le a
    have h3 := Net.c_le h.is hab
    simp only [size_prod, size_bits, hz', hθ']
    omega
end Eight.SecNetworks
