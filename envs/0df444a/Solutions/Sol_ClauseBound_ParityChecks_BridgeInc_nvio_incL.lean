-- Prove2me | solution 1 for ClauseBound.ParityChecks.BridgeInc.nvio_incL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:38:14.969426+00:00
-- url     : https://prove2.me/submissions/1b8d36f7-a748-4cc9-803a-358c2f43a2b8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_NetDefs
import Definitions.Def_ClauseBound_ParityChecks_Dummy
import Definitions.Def_ClauseBound_ParityChecks_BridgeInc
import Theorems.Thm_ClauseBound_ParityChecks_BridgeInc_nvio_incL_sum
import Theorems.Thm_ClauseBound_ParityChecks_BridgeInc_cnt_eq
import Theorems.Thm_ClauseBound_ParityChecks_BridgeInc_sum_checks
import Theorems.Thm_ClauseBound_ParityChecks_Dummy_card_inc
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
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
open Finset Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.BridgeInc
namespace ClauseBound.ParityChecks.BridgeInc
theorem _root_.solution {n r j : ℕ} {ψ : Fml} {Lam : List (List ℕ)} (h : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) (hL : WfC ψ r Lam) (hj : j ≤ r) (σ : Fin (n + r) → Bool) :
    nvio (ext σ) (incL n ψ Lam j) = #(Dummy.inc (Vof (n := n) ψ) r (Lof ψ Lam) (J1 r j) (J2 r j) (xi σ) (yy σ)) := by
  rw [nvio_incL_sum, Dummy.card_inc, sum_checks σ _ hj]
  have e2 : ∀ j' : Fin r, j' ∈ J2 r j ↔ j'.val = j := fun j' => by simp [J2]
  have h2 : cnt (ext σ) ψ Lam j = ∑ j' : Fin r, if j' ∈ J2 r j then cnt (ext σ) ψ Lam j'.val else 0 := by
    rcases Nat.lt_or_ge j r with hlt | hge
    · rw [sum_eq_single (⟨j, hlt⟩ : Fin r)]
      · rw [if_pos ((e2 _).2 rfl)]
      · intro b _ hb
        exact if_neg fun h' => hb (Fin.ext ((e2 b).1 h'))
      · intro h'
        exact absurd (mem_univ _) h'
    · rw [sum_eq_zero fun j' _ => if_neg fun h' => by have := (e2 j').1 h'; have := j'.2; omega]
      unfold cnt
      rw [List.getD_eq_default _ _ (by rw [hL.1]; exact hge)]
      rfl
  rw [h2, ← sum_add_distrib]
  refine sum_congr rfl fun j' _ => ?_
  rw [← cnt_eq σ h hL]
  have e1 : j' ∈ J1 r j ↔ j'.val < j := by simp [J1]
  simp only [e1, e2]
  rcases lt_trichotomy j'.val j with hlt | heq | hgt
  · simp [hlt, hlt.ne]
  · simp [heq]
  · simp [not_lt.2 hgt.le, hgt.ne']
end ClauseBound.ParityChecks.BridgeInc
