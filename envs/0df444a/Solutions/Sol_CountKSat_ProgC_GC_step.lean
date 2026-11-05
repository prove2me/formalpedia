-- Prove2me | solution 1 for CountKSat.ProgC.GC_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:25:36.190657+00:00
-- url     : https://prove2.me/submissions/710c5b7d-2ae5-4a8b-bd16-9bed8f48024a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_SparsifyWidthK_ProgMain
import Definitions.Def_SparsifyWidthK_SetAlg
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_SparsifyWidthK_Refine
import Mathlib.Tactic.Ring
import Definitions.Def_CountKSat_ProgC
import Theorems.Thm_CountKSat_ProgC_pick_spec
import Theorems.Thm_CountKSat_ProgC_stepC_some
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
import Theorems.Thm_WidthK_ProgMain_G_step
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
open CountKSat
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog
open CountKSat.ProgC
variable {θ : ℕ → ℕ} {k D T q leafB : ℕ} {Ok : Finset (Finset PLit) → Prop}
  {Node : Finset (Finset PLit) → Finset (Finset PLit) → ℕ → ℕ → Prop}
namespace CountKSat.ProgC
theorem _root_.solution (hθ : ∀ i, 1 ≤ θ i) (hI : Iface θ k D T q leafB Ok Node) (hR : Refines θ k) {n : ℕ} (ψ : PFml)
    (hψ : ∀ C ∈ ψ, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) (x : CNode) (p t : ℕ) (l h : CNode) (hG : GC Node ψ n k x p t)
    (hst : stepC θ k x = some (l, h)) : GC Node ψ n k l (p + 1) t ∧ GC Node ψ n k h (p + 1) (t + q) := by
  obtain ⟨H, P, hp, rfl, rfl⟩ := stepC_some hst
  obtain ⟨hHk, hHn⟩ := pick_spec hθ hI hR hψ hG.1 hp
  obtain ⟨g1, g2⟩ := ProgMain.G_step hI hR ψ x.1 p t (addP [H] x.1) (addP P x.1) hG.1 (by simp [stepK, hp])
  obtain ⟨s1, s2, s3⟩ := hG.2
  refine ⟨⟨g1, ?_, s2, s3⟩, ⟨g2, ?_, ?_, ?_⟩⟩
  · show x.2.length ≤ n + k * (p + 1)
    rw [Nat.mul_succ]; omega
  · show (negU H ++ x.2).length ≤ n + k * (p + 1)
    rw [List.length_append, negU, List.length_map, Nat.mul_succ]; omega
  · intro C hC
    rcases List.mem_append.1 hC with hC | hC
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hC
      refine ⟨by simp, fun b hb => ?_⟩
      obtain rfl : b = (a.1, !a.2) := by simpa using hb
      exact hHn a ha
    · exact s2 C hC
  · exact fun C hC => List.mem_append_right _ (s3 C hC)
end CountKSat.ProgC
