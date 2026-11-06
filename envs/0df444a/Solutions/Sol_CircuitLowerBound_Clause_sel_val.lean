-- Prove2me | solution 1 for CircuitLowerBound.Clause.sel_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:36:48.208541+00:00
-- url     : https://prove2.me/submissions/a398aa56-13e5-426a-8485-4e269601cd86

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Clause
import Theorems.Thm_CircuitLowerBound_Clause_gval_ite
import Theorems.Thm_CircuitLowerBound_Blocks_chain_all
import Theorems.Thm_CircuitLowerBound_Blocks_gval_and
import Theorems.Thm_CircuitLowerBound_Blocks_gval_andN
import Theorems.Thm_CircuitLowerBound_Blocks_num_congr
import Theorems.Thm_CircuitLowerBound_Blocks_num_testBit
import Theorems.Thm_CircuitLowerBound_Blocks_obeys_flatMap
import Theorems.Thm_CircuitLowerBound_Blocks_obeys_map
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
theorem _root_.solution {v : ℕ → Bool} {n bq bt rb R : ℕ} (h : Obeys v (n + 2) (selG n bq bt rb R)) (hO : v (n + 1) = true) {r : ℕ}
    (hr : ∀ i < rb, v (bq + bt + i) = r.testBit i) (hrl : r < 2 ^ rb) {k : ℕ} (hk : k < R) (hkl : k < 2 ^ rb) : v (Ew n rb k) = decide (r = k) := by
  rw [selG, obeys_flatMap v _ (k := rb) (selChain n bq bt rb) (fun _ => by simp [selChain]) R] at h
  have h1 := h k hk
  rw [selChain, obeys_map] at h1
  have h2 := chain_all v (n + 2 + rb * k) (n + 1) rb (fun i => decide (r.testBit i = k.testBit i)) (fun i hi => by
    rw [h1 i hi, selGate, gval_ite, gval_and, gval_andN, hr i hi]
    cases k.testBit i <;> cases r.testBit i <;> simp) rb le_rfl
  rw [Ew, h2, hO, Bool.true_and]
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  constructor
  · intro h3
    have := num_congr (b := r.testBit) (c := k.testBit) (w := rb) h3
    rwa [num_testBit, num_testBit, Nat.mod_eq_of_lt hrl, Nat.mod_eq_of_lt hkl] at this
  · rintro rfl i _
    rfl
end CircuitLowerBound.Clause
