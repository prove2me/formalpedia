-- Prove2me | solution 1 for CircuitLowerBound.Alg.pre_cases
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:04:52.119229+00:00
-- url     : https://prove2.me/submissions/7c96ec51-7978-4496-9e21-91acec1decc6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Alg_Parse
import Definitions.Def_GraphProblems_Engine
import Definitions.Def_PaddedDescent_Host
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Alg_Machine
import Theorems.Thm_CircuitLowerBound_Alg_uOf_eq
import Theorems.Thm_CircuitLowerBound_Parse_wfB_iff
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
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
import Theorems.Thm_Groundwork_TM_update_withIO
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
attribute [local simp] Groundwork.Host.upd_none
attribute [local simp] Groundwork.Host.withIO_none
attribute [local simp] Groundwork.Host.withIO_some
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
attribute [local simp] Groundwork.TM.update_withIO
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
open ENP Groundwork Turing Parse
open CircuitLowerBound.Alg
variable {F : (MCode × List Unit × ℕ) × List GateD → List Unit × Cnf} {fb : List Unit → Bool}
namespace CircuitLowerBound.Alg
theorem _root_.solution (F : (MCode × List Unit × ℕ) × List GateD → List Unit × Cnf) (fb : List Unit → Bool) (x : List Bool) :
    (pos (ones x) < top (nu (ones x)) ∧ Fits (codeOf (nu (ones x))) (ones x) (next (ones x)) ∧ WF (ones x) (decC (rest x)) ∧
        pre F fb x = F ((codeOf (nu (ones x)), List.replicate (ones x) (), next (ones x)), decC (rest x))) ∨
    (pos (ones x) < top (nu (ones x)) ∧ Fits (codeOf (nu (ones x))) (ones x) (next (ones x)) ∧ ¬WF (ones x) (decC (rest x)) ∧ pre F fb x = ([], [])) ∨
    (pos (ones x) < top (nu (ones x)) ∧ ¬Fits (codeOf (nu (ones x))) (ones x) (next (ones x)) ∧ pre F fb x = ([], [[]])) ∨
    (pos (ones x) = top (nu (ones x)) ∧ fb (List.replicate (ones x) ()) = true ∧ pre F fb x = ([], [])) ∨
    (pos (ones x) = top (nu (ones x)) ∧ fb (List.replicate (ones x) ()) = false ∧ pre F fb x = ([], [[]])) ∨
    (top (nu (ones x)) < pos (ones x) ∧ pre F fb x = ([], [[]])) := by
  unfold pre preG
  rw [uOf_eq]
  simp only [List.length_replicate]
  rcases lt_trichotomy (pos (ones x)) (top (nu (ones x))) with h | h | h
  · by_cases h2 : Fits (codeOf (nu (ones x))) (ones x) (next (ones x))
    · by_cases h3 : WF (ones x) (decC (rest x))
      · exact Or.inl ⟨h, h2, h3, by simp [h, h2, (wfB_iff _ _).2 h3]⟩
      · have h4 : wfB (ones x) (decC (rest x)) = false := by
          rw [← Bool.not_eq_true, wfB_iff]
          exact h3
        exact Or.inr (Or.inl ⟨h, h2, h3, by simp [h, h2, h4]⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h, h2, by simp [h, h2]⟩))
  · cases h5 : fb (List.replicate (ones x) ())
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h, rfl, by simp [h]⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h, rfl, by simp [h]⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h, by simp [not_lt.2 h.le, h.ne']⟩))))
end CircuitLowerBound.Alg
