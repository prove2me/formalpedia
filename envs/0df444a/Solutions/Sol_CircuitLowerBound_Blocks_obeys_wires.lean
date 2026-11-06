-- Prove2me | solution 1 for CircuitLowerBound.Blocks.obeys_wires
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:59:31.665293+00:00
-- url     : https://prove2.me/submissions/e31fc336-8c94-4161-b9aa-e52ccf7f0901

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Theorems.Thm_CircuitLowerBound_Blocks_prefix_wires
import Theorems.Thm_CircuitLowerBound_Blocks_getD_of_prefix
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
open CircuitLowerBound CircuitLowerBound.Blocks
open ENP Groundwork
namespace CircuitLowerBound.Blocks
theorem _root_.solution (x : List Bool) (C : List GateD) (h : WFa x.length C) : Obeys (fun i => (wires x (toC C)).getD i false) x.length C := by
  induction C generalizing x with
  | nil => trivial
  | cons g C ih =>
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have e : wires x (toC (g :: C)) = wires (x ++ [g.toGate.op (x.getD g.2.1 false) (x.getD g.2.2 false)]) (toC C) := rfl
    have hl : (x ++ [g.toGate.op (x.getD g.2.1 false) (x.getD g.2.2 false)]).length = x.length + 1 := by simp
    have hp := prefix_wires (x ++ [g.toGate.op (x.getD g.2.1 false) (x.getD g.2.2 false)]) (toC C)
    have ih' := ih (x ++ [g.toGate.op (x.getD g.2.1 false) (x.getD g.2.2 false)]) (by rw [hl]; exact h3)
    rw [hl] at ih'
    refine ⟨?_, by rw [e]; exact ih'⟩
    simp only [gval]
    rw [e, getD_of_prefix hp (by omega), getD_of_prefix hp (by omega), getD_of_prefix hp (by omega), List.getD_append _ _ _ _ h1,
      List.getD_append _ _ _ _ h2, List.getD_append_right _ _ _ _ le_rfl]
    simp
end CircuitLowerBound.Blocks
