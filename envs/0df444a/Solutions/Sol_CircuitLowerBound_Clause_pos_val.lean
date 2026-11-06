-- Prove2me | solution 1 for CircuitLowerBound.Clause.pos_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:43:25.697242+00:00
-- url     : https://prove2.me/submissions/3ae75ffc-615e-46f4-9567-0188d6733d2a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Clause
import Theorems.Thm_CircuitLowerBound_Clause_mod_four
import Theorems.Thm_CircuitLowerBound_Clause_posG_eqs
import Theorems.Thm_CircuitLowerBound_Blocks_full_adder
import Theorems.Thm_CircuitLowerBound_Blocks_num_congr
import Theorems.Thm_CircuitLowerBound_Blocks_num_false
import Theorems.Thm_CircuitLowerBound_Blocks_num_lt
import Theorems.Thm_CircuitLowerBound_Blocks_num_testBit
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
theorem _root_.solution {v : ℕ → Bool} {z bq P b p0 p1 : ℕ} {dW : ℕ → ℕ} (h : Obeys v b (posG z bq P b p0 p1 dW)) {md q dq : ℕ} (hz : v z = false)
    (hp0 : v p0 = md.testBit 0) (hp1 : v p1 = md.testBit 1) (hq : ∀ i < bq, v i = q.testBit i) (hql : q < 2 ^ bq)
    (hd : ∀ i < bq + 1, v (dW i) = dq.testBit i) :
    num (fun i => v (b + 1 + 7 * i + 3)) (bq + 1) = (qval P q md + dq) % 2 ^ (bq + 1) := by
  obtain ⟨e0, e⟩ := posG_eqs h
  have hadd := full_adder (fun i => v (b + 1 + 7 * i + 1)) (fun i => v (dW i)) (fun i => v (b + 1 + 7 * i + 3)) (fun i => v (cinQ z b i)) (bq + 1)
    (fun i hi => by
      obtain ⟨-, -, e2, e3, -⟩ := e i hi
      simp only [e3, e2])
    (fun i hi => by
      obtain ⟨-, -, e2, -, e4, e5, e6⟩ := e i hi
      have : cinQ z b (i + 1) = b + 1 + 7 * i + 6 := by simp [cinQ]
      simp only [this, e6, e4, e5, e2]) (bq + 1) le_rfl
  have hc0 : cinQ z b 0 = z := by simp [cinQ]
  simp only [hc0, hz] at hadd
  have hD : num (fun i => v (dW i)) (bq + 1) = dq % 2 ^ (bq + 1) := by rw [num_congr hd, num_testBit]
  have hqb : ∀ i < bq + 1, v (if i < bq then i else z) = q.testBit i := by
    intro i _
    split_ifs with hi
    · exact hq i hi
    · rw [hz]
      exact (Nat.testBit_eq_false_of_lt (hql.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)))).symm
  have hB : num (fun i => v (b + 1 + 7 * i + 1)) (bq + 1) = qval P q md % 2 ^ (bq + 1) := by
    have h4 := mod_four md
    have hb : ∀ i < bq + 1, v (b + 1 + 7 * i + 1) = (((md.testBit 0 && !md.testBit 1) && q.testBit i) || (P.testBit i && md.testBit 1)) := by
      intro i hi
      obtain ⟨e1, e2, -⟩ := e i hi
      rw [e2, e1, e0, hp0, hp1, hqb i hi]
      cases P.testBit i <;> simp
    rw [num_congr hb]
    unfold qval
    generalize md.testBit 0 = b0 at h4 ⊢
    generalize md.testBit 1 = b1 at h4 ⊢
    generalize md % 4 = m4 at h4 ⊢
    subst h4
    cases b0 <;> cases b1 <;> simp [num_false, num_testBit]
  rw [hD, hB] at hadd
  have hlt := num_lt (fun i => v (b + 1 + 7 * i + 3)) (bq + 1)
  rw [Nat.add_mod, ← Nat.add_zero (qval P q md % 2 ^ (bq + 1) + dq % 2 ^ (bq + 1))]
  have h0 : (false : Bool).toNat = 0 := rfl
  rw [h0] at hadd
  rw [← hadd, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
end CircuitLowerBound.Clause
