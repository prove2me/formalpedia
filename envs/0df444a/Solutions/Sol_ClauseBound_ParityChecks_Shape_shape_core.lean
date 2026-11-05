-- Prove2me | solution 1 for ClauseBound.ParityChecks.Shape.shape_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:47:54.313496+00:00
-- url     : https://prove2.me/submissions/6dc27cfc-8017-44a6-b8e7-5388e4216e48

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Shape
import Theorems.Thm_ClauseBound_ParityChecks_Shape_occ_eq
import Theorems.Thm_ClauseBound_ParityChecks_Shape_hasV_eq_false
import Theorems.Thm_ClauseBound_ParityChecks_Shape_length_filter_eq_card
import Theorems.Thm_ClauseBound_ParityChecks_Shape_getD_lt
import Theorems.Thm_ClauseBound_ParityChecks_Shape_wfL
import Theorems.Thm_ClauseBound_ParityChecks_Shape_occ_incL_le_of_lt
import Theorems.Thm_ClauseBound_ParityChecks_Shape_occ_incL_le_of_ge
import Theorems.Thm_ClauseBound_ParityChecks_Shape_length_incL_le
import Theorems.Thm_ClauseBound_ParityChecks_Shape_le_mul_LD
import Theorems.Thm_Groundwork_DecodeK_IsKCNF_length_le
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
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
import Theorems.Thm_Sat3_Is3CNF_length_le
attribute [local fun_prop] Groundwork.PolyT.filter
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
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Shape
open Finset Groundwork.Prog PaddedDescent.F.Mark _root_.ParityChecks ClauseBound.ParityChecks
variable {k n Δ : ℕ} {q : Par} {ψ : Fml} {Lam : List Chk} {j : ℕ}
namespace ClauseBound.ParityChecks.Shape
theorem _root_.solution (hm : ψ.length = q.m) (hnb : 1 ≤ q.nb) (h3 : q.m ≤ Δ * n) (h4 : q.m ≤ 2 * Δ * LD Δ * q.nb) (hψ : WfL k n [ψ])
    (hocc : ∀ v, (occ ψ v).length ≤ Δ) (hj : j ≤ q.r) (hL : ∀ L ∈ Lam, L.Nodup ∧ ∀ x ∈ L, x < q.m) (hT : Tent q (lam q.m Lam)) (e : ℕ) :
    WfL (k + 1) (n + q.r) [ψ, incL n ψ Lam j, ψ.drop e] ∧
      (∀ v, (occ [ψ, incL n ψ Lam j, ψ.drop e].flatten v).length ≤
        max (Δ * (2 + (Nat.clog 2 (16 * q.m) + 3 * q.r / (2 * q.nb) + 1))) (Nat.clog 2 (16 * q.r) + 3 * q.m / (2 * q.nb))) ∧
      [ψ, incL n ψ Lam j, ψ.drop e].flatten.length ≤ blkOL Δ * (n + q.r + 1) := by
  have hfl : [ψ, incL n ψ Lam j, ψ.drop e].flatten = ψ ++ (incL n ψ Lam j ++ ψ.drop e) := by simp
  refine ⟨wfL hm hψ hj hL e, fun v => ?_, ?_⟩
  · rw [hfl, occ_eq, List.filter_append, List.filter_append, List.length_append, List.length_append, ← occ_eq, ← occ_eq, ← occ_eq]
    have hd : (occ (ψ.drop e) v).length ≤ (occ ψ v).length := ((List.drop_sublist e ψ).filter _).length_le
    rcases Nat.lt_or_ge v n with hv | hv
    · refine le_trans ?_ (le_max_left _ _)
      have h1 := occ_incL_le_of_lt hm hnb (hocc v) hj hL hT hv
      have h2 := hocc v
      rw [Nat.mul_add]
      omega
    · refine le_trans ?_ (le_max_right _ _)
      have h1 := occ_incL_le_of_ge hψ hnb hj hL hT hv
      have h2 : (occ ψ v).length = 0 := by
        rw [occ_eq, length_filter_eq_card, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro x _
        rw [hasV_eq_false (getD_lt hψ x) hv]
        exact Bool.false_ne_true
      omega
  · rw [hfl, List.length_append, List.length_append, List.length_drop, hm]
    have h1 := length_incL_le (n := n) (ψ := ψ) hnb h4 hj hL hT
    have h2 : Δ * n ≤ Δ * LD Δ * n := Nat.mul_le_mul_right n (le_mul_LD Δ)
    have h5 : blkOL Δ * (n + q.r + 1) =
        2 * (Δ * n) + 16 * (Δ * LD Δ * n) + 16 * Δ * LD Δ * q.r + (2 * Δ * (q.r + 1) + 16 * Δ * LD Δ + (n + q.r + 1)) := by
      unfold blkOL
      ring
    rw [h5]
    omega
end ClauseBound.ParityChecks.Shape
