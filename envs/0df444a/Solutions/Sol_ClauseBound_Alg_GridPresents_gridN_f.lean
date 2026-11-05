-- Prove2me | solution 1 for ClauseBound.Alg.GridPresents.gridN_f
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:26:01.979207+00:00
-- url     : https://prove2.me/submissions/bbf0523c-ecf4-48ea-94d5-c5b133466683

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_GridNet
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_ClauseBound_Alg_GridPresents
import Theorems.Thm_ClauseBound_Alg_GridPresents_grid_core
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
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridPresents
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg.GridNet
variable (P : PiecesF) (pad : U) (p d : ℕ) (tr : Bool) (h ℓ y : ℕ)
variable {P pad p d tr h ℓ y}
variable (P pad p d tr h ℓ y)
namespace ClauseBound.Alg.GridPresents
theorem _root_.solution (Rm : Inst (Fin (p * d)) (List Bool)) {a b : Fin (nParts p d tr)} (hab : a ≠ b) {z θ : List Bool}
    (hz : z.length = nMemb p d tr * (p * d) * ℓ) (hθ : θ.length = capG P p d tr h ℓ y a b) :
    (gridN P pad p d tr h ℓ y Rm).f a b z θ =
      (∏ i : Fin (nMemb p d tr), if heG p d ℓ z i (nodeG d tr b i) = block ℓ i θ then 1 else 0) *
      ∏ k : Fin (nMemb p d tr) × Fin (nMemb p d tr) with k.1 < k.2, item P pad p d tr h ℓ y a b z θ k.1 k.2 := by
  have e : (gridN P pad p d tr h ℓ y Rm).f a b z θ =
      if θ ∈ (gridCl P pad p d tr h ℓ y (gridR p d tr ℓ Rm) (min a b) (max a b)).D then
        (gridNet P pad p d tr h ℓ y (gridR p d tr ℓ Rm)).f a b ((stC p d tr ℓ).dec z)
          ((gridCl P pad p d tr h ℓ y (gridR p d tr ℓ Rm) (min a b) (max a b)).dec θ) else 0 := rfl
  unfold capG at hθ
  simp only [item]
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · have h' : (a : ℕ) < b := hlt
    rw [min_eq_left h'.le, max_eq_right h'.le] at hθ
    simp only [min_eq_left h'.le, max_eq_right h'.le, if_pos h']
    have hc := grid_core (P := P) (pad := pad) (h := h) (y := y) true (gridR p d tr ℓ Rm) hlt b hz hθ
    simp only [if_true] at hc
    rw [← hc, e, min_eq_left hlt.le, max_eq_right hlt.le]
    have e' : ∀ θ', (gridNet P pad p d tr h ℓ y (gridR p d tr ℓ Rm)).f a b ((stC p d tr ℓ).dec z) θ' =
        rowTop (cutsG P pad p d tr h ℓ y) a b ((stC p d tr ℓ).dec z) θ' := fun θ' => if_pos hlt
    rw [e']
    rfl
  · have h' : (b : ℕ) < a := hlt
    rw [min_eq_right h'.le, max_eq_left h'.le] at hθ
    simp only [min_eq_right h'.le, max_eq_left h'.le, if_neg (not_lt.2 h'.le)]
    have hc := grid_core (P := P) (pad := pad) (h := h) (y := y) false (gridR p d tr ℓ Rm) hlt b hz hθ
    simp only [Bool.false_eq_true, if_false] at hc
    rw [← hc, e, min_eq_right hlt.le, max_eq_left hlt.le]
    have e' : ∀ θ', (gridNet P pad p d tr h ℓ y (gridR p d tr ℓ Rm)).f a b ((stC p d tr ℓ).dec z) θ' =
        rowBot (cutsG P pad p d tr h ℓ y) b a ((stC p d tr ℓ).dec z) θ' := fun θ' => if_neg (not_lt.2 hlt.le)
    rw [e']
    rfl
end ClauseBound.Alg.GridPresents
