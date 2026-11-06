-- Prove2me | solution 1 for CircuitLowerBound.Form.wf_check
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:58:46.109494+00:00
-- url     : https://prove2.me/submissions/714da474-6446-42a8-b33b-a906f8806177

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Definitions.Def_ToTuring_Lib_Int
import Definitions.Def_ToTuring_Lib_List3
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Nat1b
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Form
import Theorems.Thm_CircuitLowerBound_Form_wf_append
import Theorems.Thm_CircuitLowerBound_Form_length_reloc
import Theorems.Thm_CircuitLowerBound_Form_rho_lt
import Theorems.Thm_CircuitLowerBound_Form_wf_reloc
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
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Form
namespace CircuitLowerBound.Form
theorem _root_.solution {n L : ℕ} {G : List GateD} {o : List ℕ} {C : List GateD} (hL : 1 ≤ L) (hG : WF n G) (hC : WF L C)
    (ho : ∀ i, o.getD i 0 < n + G.length) : WF n (check L (n + G.length) G o C) := by
  have ho1 : ∀ i, o.getD i 0 < n + G.length + C.length := fun i => (ho i).trans_le (Nat.le_add_right _ _)
  have ho2 : ∀ i, o.getD i 0 < n + G.length + C.length + C.length := fun i => (ho1 i).trans_le (Nat.le_add_right _ _)
  rw [check, wf_append, wf_append, wf_append, wf_append]
  simp only [length_reloc]
  refine ⟨hG, wf_reloc ho _ hC, wf_reloc ho1 _ hC, wf_reloc ho2 _ hC, fun t h => ?_⟩
  have r0 := rho_lt ho 0 (show L + C.length - 1 < L + C.length by omega)
  have r1 := rho_lt ho1 (L + 1) (show L + C.length - 1 < L + C.length by omega)
  have r2 := rho_lt ho2 (L + 1 + (L + 1)) (show L + C.length - 1 < L + C.length by omega)
  have s0 := ho (0 + L)
  have s1 := ho (L + 1 + L)
  have s2 := ho (L + 1 + (L + 1) + L)
  have h5 : t < 5 := by simpa [fin] using h
  interval_cases t <;> simp only [fin, List.getElem_cons_zero, List.getElem_cons_succ] <;> constructor <;> omega
end CircuitLowerBound.Form
