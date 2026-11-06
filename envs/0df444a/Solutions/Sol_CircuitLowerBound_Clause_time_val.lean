-- Prove2me | solution 1 for CircuitLowerBound.Clause.time_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:42:34.853533+00:00
-- url     : https://prove2.me/submissions/29d109ca-f897-44e2-9cdd-2118e22634b6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Clause
import Theorems.Thm_CircuitLowerBound_Clause_mod_four
import Theorems.Thm_CircuitLowerBound_Clause_timeG_eqs
import Theorems.Thm_CircuitLowerBound_Blocks_half_adder
import Theorems.Thm_CircuitLowerBound_Blocks_num_congr
import Theorems.Thm_CircuitLowerBound_Blocks_num_false
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
theorem _root_.solution {v : ℕ → Bool} {bq bt a m0 m1 : ℕ} (h : Obeys v a (timeG bq bt a m0 m1)) {md t : ℕ} (hm0 : v m0 = md.testBit 0)
    (hm1 : v m1 = md.testBit 1) (ht : ∀ i < bt, v (bq + i) = t.testBit i) (htl : t < 2 ^ bt) :
    num (fun i => v (a + 3 + 3 * i + 1)) bt + 2 ^ bt * (v (a + 3 + 3 * bt)).toNat = tval bt t md := by
  obtain ⟨e0, e1, e2, e3, e4⟩ := timeG_eqs h
  have hadd := half_adder (fun i => v (a + 3 + 3 * i)) (fun i => v (a + 3 + 3 * i + 1)) (fun i => v (cinT a i)) bt
    (fun i hi => (e3 i hi).2.1) (fun i hi => by
      have : cinT a (i + 1) = a + 3 + 3 * i + 2 := by simp [cinT]
      simp only [this]
      exact (e3 i hi).2.2) bt le_rfl
  have hc0 : cinT a 0 = a + 1 := by simp [cinT]
  simp only [hc0] at hadd
  have hA : num (fun i => v (a + 3 + 3 * i)) bt = if v a then t else 0 := by
    cases hu : v a
    · rw [num_congr (c := fun _ => false) fun i hi => by simp [(e3 i hi).1, hu], num_false]; rfl
    · rw [num_congr (c := t.testBit) fun i hi => by simp [(e3 i hi).1, hu, ht i hi], num_testBit, Nat.mod_eq_of_lt htl]; rfl
  rw [hA, e0, e1, hm0, hm1] at hadd
  rw [e4, e2, hm0, hm1]
  have h4 := mod_four md
  have hp : 0 < 2 ^ bt := by positivity
  unfold tval
  generalize num (fun i => v (a + 3 + 3 * i + 1)) bt = S at hadd ⊢
  generalize v (cinT a bt) = cb at hadd ⊢
  generalize 2 ^ bt = p at hadd hp ⊢
  generalize md.testBit 0 = b0 at h4 hadd ⊢
  generalize md.testBit 1 = b1 at h4 hadd ⊢
  generalize md % 4 = m4 at h4 ⊢
  subst h4
  cases b0 <;> cases b1 <;> cases cb <;> simp at hadd ⊢ <;> omega
end CircuitLowerBound.Clause
