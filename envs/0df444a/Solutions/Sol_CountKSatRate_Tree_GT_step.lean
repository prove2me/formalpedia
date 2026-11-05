-- Prove2me | solution 1 for CountKSatRate.Tree.GT_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:51:39.104218+00:00
-- url     : https://prove2.me/submissions/ad2f5f72-d68d-4dc2-ae91-0bf82a6e5e56

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_CountKSat_ProgC
import Definitions.Def_CountKSat_StepCount
import Definitions.Def_CountKSat_Walk
import Definitions.Def_PaddedDescent_F_MarkDeg
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Tactic.Ring
import Definitions.Def_CountKSatRate_Tree
import Theorems.Thm_CountKSat_ProgC_pick_spec
import Theorems.Thm_CountKSat_ProgC_stepC_some
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_all
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
import Theorems.Thm_WidthK_ProgMain_G_step
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length
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
open CountKSatRate
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat WidthK.Prog
open WidthK (theta bsum leafC Iface Refines)
open CountKSatRate.Tree
variable {θ : ℕ → ℕ} {k D T q leafB : ℕ} {Ok : Finset (Finset PLit) → Prop}
  {Node : Finset (Finset PLit) → Finset (Finset PLit) → ℕ → ℕ → Prop}
namespace CountKSatRate.Tree
theorem _root_.solution (hθ : ∀ i, 1 ≤ θ i) (hI : Iface θ k D T q leafB Ok Node) (hR : Refines θ k) {n : ℕ} (ψ : PFml)
    (hψ : ∀ C ∈ ψ, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) (x : CNode) (p t : ℕ) (l h : CNode) (hG : GT Node ψ n k q x p t)
    (hst : stepC θ k x = some (l, h)) : GT Node ψ n k q l (p + 1) t ∧ GT Node ψ n k q h (p + 1) (t + q) := by
  obtain ⟨H, P, hp, rfl, rfl⟩ := ProgC.stepC_some hst
  obtain ⟨hHk, hHn⟩ := ProgC.pick_spec hθ hI hR hψ hG.1 hp
  obtain ⟨g1, g2⟩ := WidthK.ProgMain.G_step hI hR ψ x.1 p t (addP [H] x.1) (addP P x.1) hG.1 (by simp [stepK, hp])
  obtain ⟨s1, s2, s3, s4⟩ := hG.2
  refine ⟨⟨g1, s1, s2, s3, s4⟩, ⟨g2, ?_, ?_, ?_, ?_⟩⟩
  · show (negU H ++ x.2).length * q ≤ n * q + k * (t + q)
    rw [List.length_append, negU, List.length_map, Nat.add_mul, Nat.mul_add]
    have := Nat.mul_le_mul_right q hHk
    omega
  · intro C hC
    rcases List.mem_append.1 hC with hC | hC
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hC
      refine ⟨by simp, fun b hb => ?_⟩
      obtain rfl : b = (a.1, !a.2) := by simpa using hb
      exact hHn a ha
    · exact s2 C hC
  · exact fun C hC => List.mem_append_right _ (s3 C hC)
  · intro C hC
    rcases List.mem_append.1 hC with hC | hC
    · obtain ⟨a, -, rfl⟩ := List.mem_map.1 hC
      exact Or.inr ⟨_, rfl⟩
    · exact s4 C hC
end CountKSatRate.Tree
