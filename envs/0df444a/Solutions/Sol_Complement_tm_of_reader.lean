-- Prove2me | solution 1 for Complement.tm_of_reader
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:09:09.697776+00:00
-- url     : https://prove2.me/submissions/1bf8a534-c1f6-4d07-9c09-4a8794aaee20

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Complement_Defs
import Definitions.Def_Complement_Readers
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Host
import Definitions.Def_ToTuring_Poly_Basic
import Mathlib.Tactic
import Definitions.Def_Complement_Main
import Theorems.Thm_GraphProblems_length_codeWith
import Theorems.Thm_GraphProblems_stMatrixLength
import Theorems.Thm_GraphProblems_tm_of_stepped
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_mapOut_runs
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_Run_trans
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
import Theorems.Thm_Paper_Achievable_mono
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
open Complement
open Groundwork Groundwork.Prog CountKSat GraphProblems Turing
namespace Complement
theorem _root_.solution (Ms : Stepped (List Bool) ℕ) (hp : Nonempty (IsPolyT Ms)) (f : ∀ n : ℕ, SimpleGraph (Fin n) → ℕ → ℕ) {δ : ℝ} (hδ : 0 < δ) (c : ℕ)
    (h : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : ℕ), s ≤ n → ∃ T : ℕ, Ms.Runs (codeWith G s) T (c * (n + n * n + 2) ^ c) (f n G s) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ / 2 * n))
    (post : ℕ → List Bool) (hpost : PolyT post) :
    ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : ℕ), s ≤ n →
      Outputs M (codeWith G s) (post (f n G s)) ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
  obtain ⟨hp⟩ := hp
  have := IsPolyT.mapOut (M := Ms) hpost
  obtain ⟨M, C, hfin, hM⟩ := tm_of_stepped (Stepped.mapOut Ms post) (ι := Inst)
    (fun x => codeWith x.2.1 x.2.2.1) (fun x => post (f x.1 x.2.1 x.2.2.1)) (fun x => x.1) hδ (2 * c) 1 2
    (fun x => by
      obtain ⟨n, G, s, hs⟩ := x
      simp only [length_codeWith stMatrixLength]
      nlinarith)
    (fun x => by
      obtain ⟨n, G, s, hs⟩ := x
      obtain ⟨T, hr, hT⟩ := h n G s hs
      refine ⟨T, (Stepped.mapOut_runs hr).mono le_rfl ?_, hT.trans ?_⟩
      · have h1 : n + n * n + 2 ≤ (n + 2) ^ 2 := by nlinarith
        calc c * (n + n * n + 2) ^ c ≤ c * ((n + 2) ^ 2) ^ c := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 c)
          _ = c * (n + 2) ^ (2 * c) := by rw [← pow_mul]
          _ ≤ 2 * c * (n + 2) ^ (2 * c) := Nat.mul_le_mul_right _ (by omega)
      · refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        push_cast
        have : (0 : ℝ) ≤ c := Nat.cast_nonneg c
        linarith)
  exact ⟨M, C, hfin, fun n G s hs => hM ⟨n, G, s, hs⟩⟩
end Complement
