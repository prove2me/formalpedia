-- Prove2me | solution 1 for CircuitLowerBound.Form.check_out
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:58:47.319336+00:00
-- url     : https://prove2.me/submissions/6df74052-9f6f-48a4-be83-beed0d336696

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
import Theorems.Thm_CircuitLowerBound_Form_ge_append
import Theorems.Thm_CircuitLowerBound_Form_seg
import Theorems.Thm_CircuitLowerBound_Form_length_reloc
import Theorems.Thm_CircuitLowerBound_Form_copy_out
import Theorems.Thm_CircuitLowerBound_Form_xor_op
import Theorems.Thm_CircuitLowerBound_Form_and_op
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
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
attribute [local fun_prop] Groundwork.PolyT.map
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
theorem _root_.solution (a : ℕ → Bool) {n L : ℕ} {G : List GateD} {o : List ℕ} {C : List GateD} (hL : 1 ≤ L) (hG : WF n G) (hC : WF L C)
    (ho : ∀ i, o.getD i 0 < n + G.length) (hE : GE a n (check L (n + G.length) G o C)) :
    a (n + G.length + C.length + C.length + C.length + 4) = true ↔
      ∀ off ∈ [0, L + 1, L + 1 + (L + 1)],
        eval (toC C) ((List.range L).map fun k => (wires ((List.range n).map a) (toC G)).getD (o.getD (off + k) 0) false) ≠
          (wires ((List.range n).map a) (toC G)).getD (o.getD (off + L) 0) false := by
  rw [check, ge_append, ge_append, ge_append, ge_append] at hE
  simp only [length_reloc] at hE
  obtain ⟨hg, h0, h1, h2, hf⟩ := hE
  have hW : ∀ k, k < n + G.length → a k = (wires ((List.range n).map a) (toC G)).getD k false :=
    fun k hk => seg a n n id G hG (fun _ => rfl) hg k hk
  have hin : ∀ off, ((List.range L).map fun k => a (o.getD (off + k) 0))
      = (List.range L).map fun k => (wires ((List.range n).map a) (toC G)).getD (o.getD (off + k) 0) false :=
    fun off => List.map_congr_left fun k _ => hW _ (ho _)
  have c0 := copy_out a o 0 hL hC h0
  have c1 := copy_out a o (L + 1) hL hC h1
  have c2 := copy_out a o (L + 1 + (L + 1)) hL hC h2
  rw [hin] at c0 c1 c2
  have e0 := hf 0 (by simp [fin])
  have e1 := hf 1 (by simp [fin])
  have e2 := hf 2 (by simp [fin])
  have e3 := hf 3 (by simp [fin])
  have e4 := hf 4 (by simp [fin])
  simp only [fin, List.getElem_cons_zero, List.getElem_cons_succ, xor_op, and_op] at e0 e1 e2 e3 e4
  rw [c0, hW _ (ho _)] at e0
  rw [c1, hW _ (ho _)] at e1
  rw [c2, hW _ (ho _)] at e2
  rw [Nat.add_zero] at e0
  rw [e4, e3, e0, e1, e2]
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, Bool.and_eq_true, bne_iff_ne, ne_eq, and_assoc]
end CircuitLowerBound.Form
