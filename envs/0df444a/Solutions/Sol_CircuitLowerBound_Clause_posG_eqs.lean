-- Prove2me | solution 1 for CircuitLowerBound.Clause.posG_eqs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:36:47.023304+00:00
-- url     : https://prove2.me/submissions/8d039019-f46d-4d1d-8370-e67b2eccd808

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Clause
import Theorems.Thm_CircuitLowerBound_Clause_gval_ite
import Theorems.Thm_CircuitLowerBound_Blocks_gval_and
import Theorems.Thm_CircuitLowerBound_Blocks_gval_andN
import Theorems.Thm_CircuitLowerBound_Blocks_gval_fst
import Theorems.Thm_CircuitLowerBound_Blocks_gval_or
import Theorems.Thm_CircuitLowerBound_Blocks_gval_xor
import Theorems.Thm_CircuitLowerBound_Blocks_obeys_append
import Theorems.Thm_CircuitLowerBound_Blocks_obeys_flatMap
import Theorems.Thm_Groundwork_PolyT_testBit
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
attribute [local fun_prop] Groundwork.PolyT.testBit
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
open CircuitLowerBound CircuitLowerBound.Clause
open ENP Groundwork CircuitLowerBound.Blocks
namespace CircuitLowerBound.Clause
theorem _root_.solution {v : ℕ → Bool} {z bq P b p0 p1 : ℕ} {dW : ℕ → ℕ} (h : Obeys v b (posG z bq P b p0 p1 dW)) :
    v b = (v p0 && !v p1) ∧ ∀ i < bq + 1,
      v (b + 1 + 7 * i) = (v b && v (if i < bq then i else z)) ∧
      v (b + 1 + 7 * i + 1) = (if P.testBit i then (v (b + 1 + 7 * i) || v p1) else v (b + 1 + 7 * i)) ∧
      v (b + 1 + 7 * i + 2) = (v (b + 1 + 7 * i + 1) ^^ v (dW i)) ∧
      v (b + 1 + 7 * i + 3) = (v (b + 1 + 7 * i + 2) ^^ v (cinQ z b i)) ∧
      v (b + 1 + 7 * i + 4) = (v (b + 1 + 7 * i + 1) && v (dW i)) ∧
      v (b + 1 + 7 * i + 5) = (v (b + 1 + 7 * i + 2) && v (cinQ z b i)) ∧
      v (b + 1 + 7 * i + 6) = (v (b + 1 + 7 * i + 4) || v (b + 1 + 7 * i + 5)) := by
  rw [posG, obeys_append, obeys_flatMap v _ (k := 7) (posBit z bq P b p1 dW) (fun _ => rfl) (bq + 1)] at h
  obtain ⟨h1, h2⟩ := h
  simp only [Obeys, gval_andN, and_true] at h1
  refine ⟨h1, fun i hi => ?_⟩
  have h4 := h2 i hi
  simp only [posBit, Obeys, gval_xor, gval_and, gval_or, gval_ite, gval_fst, and_true, List.length_cons, List.length_nil] at h4
  exact ⟨h4.1, h4.2.1, h4.2.2.1, h4.2.2.2.1, h4.2.2.2.2.1, h4.2.2.2.2.2.1, h4.2.2.2.2.2.2⟩
end CircuitLowerBound.Clause
