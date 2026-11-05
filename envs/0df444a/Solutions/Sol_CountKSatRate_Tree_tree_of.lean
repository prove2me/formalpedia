-- Prove2me | solution 1 for CountKSatRate.Tree.tree_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:54:35.102344+00:00
-- url     : https://prove2.me/submissions/5f7b5bd6-d449-4c9c-9498-c544f79b31cc

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
import Theorems.Thm_CountKSatRate_Tree_GT_step
import Theorems.Thm_CountKSatRate_Tree_sideT_taut
import Theorems.Thm_CountKSat_ProgC_clause_of_G
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_Sparsify_exists_of_mem_leaves
import Theorems.Thm_Groundwork_Sparsify_length_leaves_le
import Theorems.Thm_Groundwork_Sparsify_stack_bound
import Theorems.Thm_Groundwork_Sparsify_step_eq_none_of_mem_leaves
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
import Theorems.Thm_WidthK_Node_bound
import Theorems.Thm_WidthK_ProgMain_card_le_of_clause
import Theorems.Thm_WidthK_ProgMain_mem_toFin
import Theorems.Thm_WidthK_ProgMain_nf_length_eq
import Theorems.Thm_WidthK_Refine_mem_toFin
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum
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
theorem _root_.solution (hSC : StStepCount) (hRC : StRootCount) (hSL : StSumLeaves) (hθ : ∀ i, 1 ≤ θ i) {n : ℕ} (hI : Iface θ k D T q leafB Ok Node)
    (hR : Refines θ k) {hv B : ℕ} (hT : T < (hv + 1) * q) (hB : n * q + k * T ≤ B * q) (ψ : PFml) (hOk : Ok (toFin ψ))
    (hψ : ∀ C ∈ ψ, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) :
    (leaves (stepC θ k) D (rootP ψ, taut n)).length ≤ ∑ j ∈ range (hv + 1), D.choose j ∧
    (∀ x ∈ leaves (stepC θ k) D (rootP ψ, taut n), stepC θ k x = none ∧ (leafF x).length ≤ leafB + B ∧
      (∀ C ∈ x.1, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) ∧ ∃ p t, GT Node ψ n k q x p t) ∧
    cntN n ψ = ((leaves (stepC θ k) D (rootP ψ, taut n)).map fun x => cntN n (leafF x)).sum ∧
    ∀ i, ((Sparsify.round (stepC θ k))^[i] ([(rootP ψ, taut n)], [])).1.length ≤ D + 1 ∧
      ∀ x ∈ ((Sparsify.round (stepC θ k))^[i] ([(rootP ψ, taut n)], [])).1, x.1.length ≤ ψ.length * 2 ^ k ∧ x.2.length ≤ B ∧
        (∀ C ∈ x.1, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) ∧ ∀ C ∈ x.2, C.length ≤ 2 ∧ ∀ l ∈ C, l.1 < n := by
  have hq : 0 < q := by
    rcases Nat.eq_zero_or_pos q with rfl | h
    · simp at hT
    · exact h
  have hb : ∀ s p t, GT Node ψ n k q s p t → p ≤ D ∧ t ≤ T := fun s p t h => hI.bound _ _ _ _ h.1.2
  have hs := GT_step hθ hI hR ψ hψ
  have hr : GT Node ψ n k q (rootP ψ, taut n) 0 0 :=
    ⟨⟨hR.nf_root ψ, by rw [hR.toFin_root]; exact hI.root _ hOk⟩, sideT_taut n k q⟩
  have hnone := step_eq_none_of_mem_leaves hb hs D (rootP ψ, taut n) 0 0 hr (by omega)
  have hk0 : ∀ C ∈ toFin ψ, C.card ≤ k := by
    intro X hX
    obtain ⟨C, hC, rfl⟩ := WidthK.ProgMain.mem_toFin.1 hX
    exact (List.toFinset_card_le C).trans (hψ C hC).1
  have hcl : ∀ x p t, GT Node ψ n k q x p t → ∀ C ∈ x.1, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n :=
    fun x p t hx C hC => ProgC.clause_of_G hI hψ hx.1 C hC
  have hside : ∀ x p t, GT Node ψ n k q x p t → x.2.length ≤ B := by
    intro x p t hx
    refine Nat.le_of_mul_le_mul_right ((hx.2.1.trans ?_).trans hB) hq
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (hb x p t hx).2) _
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact length_leaves_le hb hs _ _ _ _ 0 0 hr (by omega) (by omega)
  · intro x hx
    obtain ⟨p', t', hx'⟩ := exists_of_mem_leaves hs _ _ 0 0 hr x hx
    refine ⟨hnone x hx, ?_, hcl x p' t' hx', p', t', hx'⟩
    · have h1 : x.1.length ≤ leafB := by
        rw [WidthK.ProgMain.nf_length_eq hx'.1.1]
        refine hI.leaf _ _ _ _ hx'.1.2 (hR.none x.1 hx'.1.1 ?_)
        have := hnone x hx
        simpa [stepC] using this
      have h2 := hside x p' t' hx'
      rw [leafF, List.length_append]
      omega
  · have e : rootC (List.replicate n (), ψ) = (rootP ψ, taut n) := by simp [rootC]
    rw [← hRC n ψ, e]
    exact hSL _ _ _ _ hs (fun x => cntN n (leafF x)) (fun s _ _ l h _ hst => hSC θ k n s l h hst) D (rootP ψ, taut n) 0 0 hr
  · intro i
    obtain ⟨h1, h2⟩ := stack_bound hb hs (rootP ψ, taut n) 0 0 hr i
    refine ⟨h1, fun x hx => ?_⟩
    obtain ⟨p', t', hx'⟩ := h2 x hx
    refine ⟨?_, hside x p' t' hx', hcl x p' t' hx', hx'.2.2.1⟩
    rw [WidthK.ProgMain.nf_length_eq hx'.1.1]
    refine (WidthK.ProgMain.card_le_of_clause hk0 (hI.clause _ _ _ _ hx'.1.2)).trans (Nat.mul_le_mul_right _ ?_)
    rw [toFin]
    exact (List.toFinset_card_le _).trans (by simp)
end CountKSatRate.Tree
