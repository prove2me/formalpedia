-- Prove2me | solution 1 for CircuitLowerBound.Clause.timeG_eqs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:35:30.004489+00:00
-- url     : https://prove2.me/submissions/587f3b5a-b108-4ff9-93e4-b56b11d5d0a1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Clause
import Theorems.Thm_CircuitLowerBound_Blocks_gval_and
import Theorems.Thm_CircuitLowerBound_Blocks_gval_andN
import Theorems.Thm_CircuitLowerBound_Blocks_gval_or
import Theorems.Thm_CircuitLowerBound_Blocks_gval_xor
import Theorems.Thm_CircuitLowerBound_Blocks_length_flatMap_const
import Theorems.Thm_CircuitLowerBound_Blocks_obeys_append
import Theorems.Thm_CircuitLowerBound_Blocks_obeys_flatMap
import Theorems.Thm_Groundwork_PolyT_flatMap
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
attribute [local fun_prop] Groundwork.PolyT.flatMap
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
open CircuitLowerBound CircuitLowerBound.Clause
open ENP Groundwork CircuitLowerBound.Blocks
namespace CircuitLowerBound.Clause
theorem _root_.solution {v : ℕ → Bool} {bq bt a m0 m1 : ℕ} (h : Obeys v a (timeG bq bt a m0 m1)) :
    v a = (v m0 ^^ v m1) ∧ v (a + 1) = (v m1 && !v m0) ∧ v (a + 2) = (v m0 && v m1) ∧
    (∀ i < bt, v (a + 3 + 3 * i) = (v a && v (bq + i)) ∧ v (a + 3 + 3 * i + 1) = (v (a + 3 + 3 * i) ^^ v (cinT a i)) ∧
      v (a + 3 + 3 * i + 2) = (v (a + 3 + 3 * i) && v (cinT a i))) ∧
    v (a + 3 + 3 * bt) = (v (cinT a bt) || v (a + 2)) := by
  rw [timeG, obeys_append, obeys_append, obeys_flatMap v _ (k := 3) (timeBit bq a) (fun _ => rfl) bt] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hl : a + ([(opXor, m0, m1), (opAndN, m1, m0), (opAnd, m0, m1)] ++ (List.range bt).flatMap (timeBit bq a)).length = a + 3 + 3 * bt := by
    rw [List.length_append, length_flatMap_const (k := 3) (timeBit bq a) (fun _ => rfl) bt]
    simp only [List.length_cons, List.length_nil]
    omega
  rw [hl] at h3
  simp only [Obeys, gval_xor, gval_andN, gval_and, gval_or, and_true] at h1 h3
  refine ⟨h1.1, h1.2.1, h1.2.2, fun i hi => ?_, h3⟩
  have h4 := h2 i hi
  simp only [timeBit, Obeys, gval_xor, gval_and, and_true, List.length_cons, List.length_nil] at h4
  exact ⟨h4.1, h4.2.1, h4.2.2⟩
end CircuitLowerBound.Clause
