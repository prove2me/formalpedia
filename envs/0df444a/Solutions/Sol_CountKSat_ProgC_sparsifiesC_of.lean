-- Prove2me | solution 1 for CountKSat.ProgC.sparsifiesC_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:31:30.978734+00:00
-- url     : https://prove2.me/submissions/c6510f05-0a84-402d-9316-d5958eaea2aa

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
import Theorems.Thm_CountKSat_ProgC_clause_of_G
import Theorems.Thm_CountKSat_ProgC_GC_step
import Theorems.Thm_CountKSat_ProgC_mem_taut
import Theorems.Thm_CountKSat_ProgC_sideOK_taut
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
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
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
open CountKSat
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog
open CountKSat.ProgC
variable {θ : ℕ → ℕ} {k D T q leafB : ℕ} {Ok : Finset (Finset PLit) → Prop}
  {Node : Finset (Finset PLit) → Finset (Finset PLit) → ℕ → ℕ → Prop}
namespace CountKSat.ProgC
theorem _root_.solution (hSC : StStepCount) (hRC : StRootCount) (hSL : StSumLeaves) (hθ : ∀ i, 1 ≤ θ i) {n : ℕ} (hI : Iface θ k D T q leafB Ok Node) (hR : Refines θ k) {hv : ℕ}
    (hT : T < (hv + 1) * q) (ψ : PFml) (hOk : Ok (toFin ψ)) (hψ : ∀ C ∈ ψ, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) :
    (leaves (stepC θ k) D (rootP ψ, taut n)).length ≤ ∑ j ∈ range (hv + 1), D.choose j ∧
    (∀ x ∈ leaves (stepC θ k) D (rootP ψ, taut n), stepC θ k x = none ∧ (leafF x).length ≤ leafB + (n + k * D) ∧
      (∀ C ∈ leafF x, C.length ≤ max k 2 ∧ ∀ l ∈ C, l.1 < n) ∧ ∀ i < n, ∃ C ∈ leafF x, ∃ l ∈ C, l.1 = i) ∧
    cntN n ψ = ((leaves (stepC θ k) D (rootP ψ, taut n)).map fun x => cntN n (leafF x)).sum ∧
    ∀ i, ((Sparsify.round (stepC θ k))^[i] ([(rootP ψ, taut n)], [])).1.length ≤ D + 1 ∧
      ∀ x ∈ ((Sparsify.round (stepC θ k))^[i] ([(rootP ψ, taut n)], [])).1, (leafF x).length ≤ ψ.length * 2 ^ k + (n + k * D) ∧
        ∀ C ∈ leafF x, C.length ≤ max k 2 ∧ ∀ l ∈ C, l.1 < n := by
  have hb : ∀ s p t, GC Node ψ n k s p t → p ≤ D ∧ t ≤ T := fun s p t h => hI.bound _ _ _ _ h.1.2
  have hs := GC_step hθ hI hR ψ hψ
  have hr : GC Node ψ n k (rootP ψ, taut n) 0 0 :=
    ⟨⟨hR.nf_root ψ, by rw [hR.toFin_root]; exact hI.root _ hOk⟩, sideOK_taut n k⟩
  have hnone := step_eq_none_of_mem_leaves hb hs D (rootP ψ, taut n) 0 0 hr (by omega)
  have hk0 : ∀ C ∈ toFin ψ, C.card ≤ k := by
    intro X hX
    obtain ⟨C, hC, rfl⟩ := ProgMain.mem_toFin.1 hX
    exact (List.toFinset_card_le C).trans (hψ C hC).1
  have hcl : ∀ x p t, GC Node ψ n k x p t → ∀ C ∈ leafF x, C.length ≤ max k 2 ∧ ∀ l ∈ C, l.1 < n := by
    intro x p t hx C hC
    rcases List.mem_append.1 hC with hC | hC
    · exact ⟨(hx.2.2.1 C hC).1.trans (le_max_right _ _), (hx.2.2.1 C hC).2⟩
    · have := clause_of_G hI hψ hx.1 C hC
      exact ⟨this.1.trans (le_max_left _ _), this.2⟩
  have hside : ∀ x p t, GC Node ψ n k x p t → x.2.length ≤ n + k * D := by
    intro x p t hx
    exact hx.2.1.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (hb x p t hx).1) _)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact length_leaves_le hb hs _ _ _ _ 0 0 hr (by omega) (by omega)
  · intro x hx
    obtain ⟨p', t', hx'⟩ := exists_of_mem_leaves hs _ _ 0 0 hr x hx
    refine ⟨hnone x hx, ?_, hcl x p' t' hx', fun i hi => ?_⟩
    · have h1 : x.1.length ≤ leafB := by
        rw [ProgMain.nf_length_eq hx'.1.1]
        refine hI.leaf _ _ _ _ hx'.1.2 (hR.none x.1 hx'.1.1 ?_)
        have := hnone x hx
        simpa [stepC] using this
      have h2 := hside x p' t' hx'
      rw [leafF, List.length_append]
      omega
    · exact ⟨[(i, true), (i, false)], List.mem_append_left _ (hx'.2.2.2 _ (mem_taut.2 ⟨i, hi, rfl⟩)), (i, true), by simp, rfl⟩
  · have e : rootC (List.replicate n (), ψ) = (rootP ψ, taut n) := by simp [rootC]
    rw [← hRC n ψ, e]
    exact hSL _ _ _ _ hs (fun x => cntN n (leafF x)) (fun s _ _ l h _ hst => hSC θ k n s l h hst) D (rootP ψ, taut n) 0 0 hr
  · intro i
    obtain ⟨h1, h2⟩ := stack_bound hb hs (rootP ψ, taut n) 0 0 hr i
    refine ⟨h1, fun x hx => ?_⟩
    obtain ⟨p', t', hx'⟩ := h2 x hx
    refine ⟨?_, hcl x p' t' hx'⟩
    have h3 : x.1.length ≤ ψ.length * 2 ^ k := by
      rw [ProgMain.nf_length_eq hx'.1.1]
      refine (ProgMain.card_le_of_clause hk0 (hI.clause _ _ _ _ hx'.1.2)).trans (Nat.mul_le_mul_right _ ?_)
      rw [toFin]
      exact (List.toFinset_card_le _).trans (by simp)
    have h4 := hside x p' t' hx'
    rw [leafF, List.length_append]
    omega
end CountKSat.ProgC
