-- Prove2me | solution 1 for CircuitLowerBound.Clause.fld_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:44:16.20559+00:00
-- url     : https://prove2.me/submissions/d0e4af84-2bc6-42bc-8928-036ecdb4f43d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Clause
import Theorems.Thm_CircuitLowerBound_Clause_gval_ite
import Theorems.Thm_CircuitLowerBound_Clause_fbit_zero
import Theorems.Thm_CircuitLowerBound_Blocks_chain_any
import Theorems.Thm_CircuitLowerBound_Blocks_gval_fst
import Theorems.Thm_CircuitLowerBound_Blocks_gval_or
import Theorems.Thm_CircuitLowerBound_Blocks_obeys_flatMap
import Theorems.Thm_CircuitLowerBound_Blocks_obeys_map
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
open CircuitLowerBound CircuitLowerBound.Clause
open ENP Groundwork CircuitLowerBound.Blocks
namespace CircuitLowerBound.Clause
theorem _root_.solution {v : ℕ → Bool} {n rb kbm nf : ℕ} {tb : List TCl} (h : Obeys v (n + 2 + rb * tb.length) (fldG n rb kbm nf tb)) (hZ : v n = false) {r : ℕ}
    (hE : ∀ k < tb.length, v (Ew n rb k) = decide (r = k)) {a : ℕ} (ha : a < 3 * nf) :
    v (prevW (n + 2 + rb * tb.length + tb.length * a) n tb.length) = fbit kbm (litI (tb.getD r zeroCl) (a / nf)) (a % nf) := by
  rw [fldG, obeys_flatMap v _ (k := tb.length) (fldChain n rb kbm nf tb) (fun _ => by simp [fldChain]) (3 * nf)] at h
  have h1 := h a ha
  rw [fldChain, obeys_map] at h1
  have h2 := chain_any v (n + 2 + rb * tb.length + tb.length * a) n tb.length
    (fun k => fbit kbm (litI (tb.getD k zeroCl) (a / nf)) (a % nf) && decide (r = k)) (fun k hk => by
    rw [h1 k hk, fldGate, gval_ite, gval_or, gval_fst, hE k hk]
    cases fbit kbm (litI (tb.getD k zeroCl) (a / nf)) (a % nf) <;> simp) tb.length le_rfl
  rw [h2, hZ, Bool.false_or]
  by_cases hr : r < tb.length
  · rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, Bool.and_eq_true]
    constructor
    · rintro ⟨k, -, h3, rfl⟩
      exact h3
    · intro h3
      exact ⟨r, hr, h3, rfl⟩
  · rw [List.getD_eq_default _ _ (by omega), fbit_zero]
    simp only [decide_eq_false_iff_not, Bool.and_eq_true, decide_eq_true_eq, not_exists, not_and]
    intro k hk _ hrk
    omega
end CircuitLowerBound.Clause
