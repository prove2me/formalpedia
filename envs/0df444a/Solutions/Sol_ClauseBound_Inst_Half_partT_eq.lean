-- Prove2me | solution 1 for ClauseBound.Inst.Half.partT_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:41:35.3472+00:00
-- url     : https://prove2.me/submissions/78cde4c5-83b1-45d6-807d-09394da64f52

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_ClauseBound_Inst_HalfVal
import Theorems.Thm_ClauseBound_Inst_Half_Val_mem_labs
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_sum
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
attribute [local fun_prop] Groundwork.PolyT.sum
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
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec Finset
open Val
namespace ClauseBound.Inst.Half
theorem _root_.solution (hT : StTopF) (hB : StBotF) {h : ℕ} (hh : 1 ≤ h) {pad : U} (hp : padLen h ≤ pad.length) (tr top : Bool) (s : ℤ) (a b θ : List Bool)
    (ha : encF (allTab (4 * h)) h a ∈ (allTab (4 * h)).flatten ∧ (encF (allTab (4 * h)) h a).sum = h)
    (hb : encF (allTab (4 * h)) h b ∈ (allTab (4 * h)).flatten ∧ (encF (allTab (4 * h)) h b).sum = h) :
    partT pad tr top h s (allTab (4 * h)) a b θ =
      ((labs (allTab (4 * h)) tr h s)[ofWord θ]?).elim 0 (valK tr top h s (encF (allTab (4 * h)) h a) (encF (allTab (4 * h)) h b)) := by
  unfold partT
  cases hq : (labs (allTab (4 * h)) tr h s)[ofWord θ]? with
  | none => rfl
  | some p =>
    obtain ⟨h1, h2⟩ := mem_labs (List.mem_of_getElem? hq)
    simp only [Option.elim]
    cases top <;> cases tr <;> simp only [valK, cond_true, cond_false]
    · exact hB pad h hh hp _ hb.1 hb.2 _ _ ha.1 _ h2
    · exact hB pad h hh hp _ hb.1 hb.2 _ _ h2 _ ha.1
    · exact hT pad h hh hp _ ha.1 ha.2 _ h1 _ _ h2 _ hb.1
    · exact hT pad h hh hp _ ha.1 ha.2 _ h1 _ _ hb.1 _ h2
end ClauseBound.Inst.Half
