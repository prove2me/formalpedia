-- Prove2me | solution 1 for ClauseBound.ParityChecks.Shape.occ_incL_le_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:38:13.590816+00:00
-- url     : https://prove2.me/submissions/5c4ba3f8-9b32-4974-a622-866d15ead11f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Shape
import Theorems.Thm_ClauseBound_ParityChecks_Shape_occ_eq
import Theorems.Thm_ClauseBound_ParityChecks_Shape_hasV_append_singleton
import Theorems.Thm_ClauseBound_ParityChecks_Shape_countP_eq_card
import Theorems.Thm_ClauseBound_ParityChecks_Shape_length_filter_eq_card
import Theorems.Thm_ClauseBound_ParityChecks_Shape_getD_ok
import Theorems.Thm_ClauseBound_ParityChecks_Shape_length_occ_incL
import Theorems.Thm_ClauseBound_ParityChecks_Shape_card_col_le
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_key
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_countP
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
attribute [local fun_prop] Groundwork.PolyT.countP
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
theorem _root_.solution (hm : ψ.length = q.m) (hnb : 1 ≤ q.nb) {v : ℕ} (hocc : (occ ψ v).length ≤ Δ) (hj : j ≤ q.r)
    (hL : ∀ L ∈ Lam, L.Nodup ∧ ∀ x ∈ L, x < q.m) (hT : Tent q (lam q.m Lam)) (hv : v < n) :
    (occ (incL n ψ Lam j) v).length ≤ Δ * (Nat.clog 2 (16 * q.m) + 3 * q.r / (2 * q.nb) + 1) := by
  have e1 : ∀ j' x, hasV v (ψ.getD x [] ++ [(n + j', false)]) = hasV v (ψ.getD x []) := fun j' x => by
    have h : (n + j' == v) = false := by
      rw [beq_eq_false_iff_ne]
      omega
    rw [hasV_append_singleton, h, Bool.or_false]
  have e2 : ∀ j', ((Lam.getD j' []).countP fun x => hasV v (ψ.getD x [])) =
      #{x ∈ range q.m | x ∈ Lam.getD j' [] ∧ hasV v (ψ.getD x []) = true} := fun j' =>
    countP_eq_card (getD_ok hL j').1 (getD_ok hL j').2 _
  rw [length_occ_incL]
  simp only [e1]
  rw [← Finset.sum_range_succ fun j' => (Lam.getD j' []).countP fun x => hasV v (ψ.getD x [])]
  simp only [e2]
  have key : ∑ j' ∈ range (j + 1), #{x ∈ range q.m | x ∈ Lam.getD j' [] ∧ hasV v (ψ.getD x []) = true} =
      ∑ x ∈ range q.m, #{j' ∈ range (j + 1) | x ∈ Lam.getD j' [] ∧ hasV v (ψ.getD x []) = true} :=
    Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow fun j' x => x ∈ Lam.getD j' [] ∧ hasV v (ψ.getD x []) = true
  rw [key]
  have hx : ∀ x ∈ range q.m, #{j' ∈ range (j + 1) | x ∈ Lam.getD j' [] ∧ hasV v (ψ.getD x []) = true} ≤
      if hasV v (ψ.getD x []) = true then Nat.clog 2 (16 * q.m) + 3 * q.r / (2 * q.nb) + 1 else 0 := by
    intro x hx
    split_ifs with hP
    · refine le_trans (Finset.card_le_card ?_) (card_col_le hnb hj hT (Finset.mem_range.1 hx))
      exact fun j' hj' => Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hj').1, (Finset.mem_filter.1 hj').2.1⟩
    · rw [Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun j' _ h => hP h.2
  refine (Finset.sum_le_sum hx).trans ?_
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, ← hm, ← length_filter_eq_card, ← occ_eq]
  exact Nat.mul_le_mul_right _ hocc
end ClauseBound.ParityChecks.Shape
