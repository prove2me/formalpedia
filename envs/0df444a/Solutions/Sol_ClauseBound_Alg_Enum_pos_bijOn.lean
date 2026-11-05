-- Prove2me | solution 1 for ClauseBound.Alg.Enum.pos_bijOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:51:21.231662+00:00
-- url     : https://prove2.me/submissions/5261ab7d-e992-4abb-b5a3-14c59df7fe66

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_StepMachines_Math_CodeSeq
import Definitions.Def_Groundwork_Net_Net
import Definitions.Def_ClauseBound_Alg_Enum
import Theorems.Thm_ClauseBound_Alg_Enum_pos_div
import Theorems.Thm_ClauseBound_Alg_Enum_pos_mod
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
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Enum
open Finset Groundwork Groundwork.Prog PaddedDescent.F
variable {g : ℕ}
namespace ClauseBound.Alg.Enum
theorem _root_.solution : Set.BijOn (pos (g := g)) {_p | True} (range (g * g)) := by
  refine ⟨fun p _ => ?_, fun p _ q _ h => ?_, fun j hj => ?_⟩
  · have h1 : (p.1.val + 1) * g ≤ g * g := Nat.mul_le_mul_right g p.1.2
    have h2 := p.2.2
    rw [Nat.succ_mul] at h1
    exact mem_coe.2 (mem_range.2 (by unfold pos; omega))
  · exact Prod.ext (Fin.ext (by rw [← pos_div p, h, pos_div])) (Fin.ext (by rw [← pos_mod p, h, pos_mod]))
  · have hj : j < g * g := mem_range.1 (mem_coe.1 hj)
    have hg : 0 < g := Nat.pos_of_ne_zero fun e => by simp [e] at hj
    exact ⟨(⟨j / g, Nat.div_lt_of_lt_mul hj⟩, ⟨j % g, Nat.mod_lt _ hg⟩), trivial, Nat.div_add_mod' j g⟩
end ClauseBound.Alg.Enum
