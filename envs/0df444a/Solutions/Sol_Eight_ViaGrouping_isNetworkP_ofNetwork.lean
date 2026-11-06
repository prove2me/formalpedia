-- Prove2me | solution 1 for Eight.ViaGrouping.isNetworkP_ofNetwork
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:00:08.680229+00:00
-- url     : https://prove2.me/submissions/a81ffed1-9759-4b81-bd79-80d3a58215d7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Bridge
import Theorems.Thm_Eight_ViaGrouping_is_ofNetwork
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_const_runs
import Theorems.Thm_Groundwork_Stepped_mapIn_runs
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
import Theorems.Thm_PaddedDescent_F_cap_eq
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
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Finset Stepped Eight.SecNetworks
variable {g : ℕ}
namespace Eight.ViaGrouping
theorem _root_.solution {C : Type} [HasSize C] {Np : Paper.NetworkProcedures C} {Pf : C → ℕ} {Q : Stepped (C × PsiQ) ℤ} {c : C}
    {N : Paper.Network (Fin g) (List Bool) (List Bool)} {P B τ S : ℕ} (hP : 1 ≤ P) (hτ : 1 ≤ τ) (h : Paper.IsNetwork Np c N P B τ S) (hPf : Pf c = P)
    (hQ : ∀ a b : Fin g, a ≠ b → ∀ z ∈ N.S a, ∀ z' ∈ N.S b, Q.Runs (c, ((a.val, b.val), (z, z'))) τ S (N.Ψ a b z z')) :
    IsNetworkP (ofProcs Np Pf Q) c (ofNetwork N fun a => Np.n c a) P (B + 1) τ (S + 2) where
  is := is_ofNetwork hP h
  τ_pos := hτ
  given :=
  { P_eq := hPf
    len_eq := fun _ => rfl
    cap_eq := fun a b hab => (h.presented.c_eq a b hab).symm
    mem_runs := fun a z hz => by
      have hz' : z.length = Np.n c a := hz
      have hmem : decide (z ∈ (ofNetwork N fun a => Np.n c a).S a) = true := by
        change decide (z ∈ N.S a) = true
        rw [h.presented.S_eq a]
        exact decide_eq_true (mem_words.2 hz')
      rw [hmem]
      refine (mapIn_runs (f := fun _ : C × WQ => ()) (a := (c, (a.val, z))) (const_runs true ())).mono hτ ?_
      simp only [size_unit, size_bool]
      omega
    W_runs := fun a z hz => by
      have hz' : z ∈ N.S a := hz
      rw [h.presented.S_eq a] at hz'
      exact (h.presented.W_runs a z (mem_words.1 hz')).mono le_rfl (by omega)
    Ψ_runs := fun a b hab z hz z' hz' => (hQ a b hab z hz z' hz').mono le_rfl (by omega)
    f_runs := fun a b hab z hz θ hθ => by
      have hz' : z ∈ N.S a := hz
      rw [h.presented.S_eq a] at hz'
      have hθ' : θ ∈ words (N.c a b) := hθ
      rw [h.presented.c_eq a b hab] at hθ'
      exact (h.presented.f_runs a b z θ hab (mem_words.1 hz') (mem_words.1 hθ')).mono le_rfl (by omega) }
end Eight.ViaGrouping
