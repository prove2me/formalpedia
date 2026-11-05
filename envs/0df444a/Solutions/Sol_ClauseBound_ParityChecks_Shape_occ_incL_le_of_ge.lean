-- Prove2me | solution 1 for ClauseBound.ParityChecks.Shape.occ_incL_le_of_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:30:58.99711+00:00
-- url     : https://prove2.me/submissions/fdb6bf9d-f28a-496c-9479-3f19fe441a56

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Shape
import Theorems.Thm_ClauseBound_ParityChecks_Shape_le_of_two_pow_lt
import Theorems.Thm_ClauseBound_ParityChecks_Shape_hasV_append_singleton
import Theorems.Thm_ClauseBound_ParityChecks_Shape_hasV_eq_false
import Theorems.Thm_ClauseBound_ParityChecks_Shape_card_lam
import Theorems.Thm_ClauseBound_ParityChecks_Shape_getD_ok
import Theorems.Thm_ClauseBound_ParityChecks_Shape_getD_lt
import Theorems.Thm_ClauseBound_ParityChecks_Shape_length_occ_incL
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_countP
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
theorem _root_.solution (hψ : WfL k n [ψ]) (hnb : 1 ≤ q.nb) (hj : j ≤ q.r) (hL : ∀ L ∈ Lam, L.Nodup ∧ ∀ x ∈ L, x < q.m)
    (hT : Tent q (lam q.m Lam)) {v : ℕ} (hv : n ≤ v) :
    (occ (incL n ψ Lam j) v).length ≤ Nat.clog 2 (16 * q.r) + 3 * q.m / (2 * q.nb) := by
  have e0 : ∀ x, hasV v (ψ.getD x []) = false := fun x => hasV_eq_false (getD_lt hψ x) hv
  have e1 : ∀ j', ((Lam.getD j' []).countP fun x => hasV v (ψ.getD x [] ++ [(n + j', false)])) =
      if j' = v - n then (Lam.getD j' []).length else 0 := fun j' => by
    simp only [hasV_append_singleton, e0, Bool.false_or]
    split_ifs with h
    · have h' : (n + j' == v) = true := by
        rw [beq_iff_eq]
        omega
      rw [h', List.countP_true]
    · have h' : (n + j' == v) = false := by
        rw [beq_eq_false_iff_ne]
        omega
      rw [h', List.countP_false]
      rfl
  have e2 : ((Lam.getD j []).countP fun x => hasV v (ψ.getD x [])) = 0 := by
    simp only [e0]
    rw [List.countP_false]
    rfl
  rw [length_occ_incL, e2, add_zero]
  simp only [e1]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · have hr : v - n < q.r := (Finset.mem_range.1 h).trans_le hj
    rw [← card_lam Lam (v - n) (getD_ok hL _).1 (getD_ok hL _).2]
    exact le_of_two_pow_lt hnb (hT.row _ hr)
  · exact Nat.zero_le _
end ClauseBound.ParityChecks.Shape
