-- Prove2me | solution 1 for Eight.ViaGrouping.Table.termP_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:34:25.851336+00:00
-- url     : https://prove2.me/submissions/1e8e3621-049a-4c5e-b392-f59a64689c04

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Table
import Theorems.Thm_Eight_ViaGrouping_Table_mem_members
import Theorems.Thm_Eight_ViaGrouping_Table_natAbs_le
import Theorems.Thm_Eight_ViaGrouping_Table_length_zA
import Theorems.Thm_Eight_ViaGrouping_Table_length_labOf
import Theorems.Thm_Eight_ViaGrouping_Table_gate_runs
import Theorems.Thm_Eight_ViaGrouping_Table_f_toPaperNetwork
import Theorems.Thm_Eight_ViaGrouping_Table_psi_toPaperNetwork
import Theorems.Thm_Eight_ViaGrouping_Table_sum_valF
import Theorems.Thm_Eight_SecNetworks_Net_sized_toPaperNetwork
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_NetE_length_labOf
import Theorems.Thm_Groundwork_Prog_NetE_length_zA
import Theorems.Thm_Groundwork_Prog_NetE_mem_members
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Sparsify_StackOK_mem
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_const_runs
import Theorems.Thm_Groundwork_Stepped_ite_runs_false
import Theorems.Thm_Groundwork_Stepped_ite_runs_true
import Theorems.Thm_Groundwork_Stepped_mapIn_runs
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
import Theorems.Thm_PaddedDescent_F_cap_eq
import Theorems.Thm_Paper_Achievable_mono
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
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Eight.ViaGrouping.Table
variable {C : Type} [HasSize C] {K g : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
variable {x β : ℕ} {G : Fin K} {θ : Fin K → List Bool}
namespace Eight.ViaGrouping.Table
theorem _root_.solution (h : IsNetworkP Np c N P B τ S) (hβ : ∀ G < K, ∀ G' < K, G ≠ G' → lbLen K g Np.toPaperNetwork c x G G' ≤ β)
    (hθ : ∀ G', G' ≠ G → (θ G').length = β) (y : ℕ) {i : ℕ} (hi : i < g * g) :
    (termP K g Np).Runs ((((c, x), (G.val, List.ofFn θ)), y), i) (4 * τ + 3) (2 * size ((((c, x), (G.val, List.ofFn θ)), y), i) + S + 12)
      (termVal K g Np.toPaperNetwork N.toPaperNetwork ((((c, x), (G.val, List.ofFn θ)), y), i)) ∧
    (termVal K g Np.toPaperNetwork N.toPaperNetwork ((((c, x), (G.val, List.ofFn θ)), y), i)).natAbs ≤ 2 ^ B := by
  have hg : 0 < g := Nat.pos_of_ne_zero fun h => by simp [h] at hi
  have ha : i / g < g := Nat.div_lt_of_lt_mul hi
  have hb : i % g < g := Nat.mod_lt _ hg
  have h2B : 1 ≤ 2 ^ B := Nat.one_le_two_pow
  have hτ := h.τ_pos
  have hS := Net.sized_toPaperNetwork h.is
  cases h1 : isOne K g ((((c, x), (G.val, List.ofFn θ)), y), i) with
  | true =>
    have ev : termVal K g Np.toPaperNetwork N.toPaperNetwork ((((c, x), (G.val, List.ofFn θ)), y), i) = 1 := by
      simp only [termVal, h1, if_true]
    rw [ev]
    refine ⟨(ite_runs_true h1 (const_runs (1 : ℤ) _)).mono (by omega) ?_, by simpa using h2B⟩
    simp only [size_prod, size_nat, size_int]
    have : (1 : ℤ).natAbs.size = 1 := rfl
    omega
  | false =>
    have hcolA : col K x (i / g) = G.val := by
      by_contra hne
      have : isOne K g ((((c, x), (G.val, List.ofFn θ)), y), i) = true := by simp [isOne, hne]
      rw [h1] at this
      cases this
    have ham : i / g ∈ members K g x G := mem_members.2 ⟨ha, hcolA⟩
    have hza : (zA K g Np.toPaperNetwork (((c, x), (G.val, List.ofFn θ)), y) (i / g)).length = N.len ⟨i / g, ha⟩ :=
      (length_zA Np.toPaperNetwork ham).trans (h.given.len_eq ⟨i / g, ha⟩)
    cases h2 : isW g ((((c, x), (G.val, List.ofFn θ)), y), i) with
    | true =>
      have ev : termVal K g Np.toPaperNetwork N.toPaperNetwork ((((c, x), (G.val, List.ofFn θ)), y), i) =
          N.toPaperNetwork.W ⟨i / g, ha⟩ (zA K g Np.toPaperNetwork (((c, x), (G.val, List.ofFn θ)), y) (i / g)) := by
        simp only [termVal, h1, h2, if_true, if_false, Bool.false_eq_true]
        exact dif_pos ha
      rw [ev]
      have r := gate_runs h (u := ((((c, x), (G.val, List.ofFn θ)), y), i)) (q := qW K g Np.toPaperNetwork) (M := mapIn (qW K g Np.toPaperNetwork) Np.W) rfl hza le_rfl le_rfl
        fun hm => mapIn_runs (h.given.W_runs ⟨i / g, ha⟩ _ hm)
      exact ⟨(ite_runs_false h1 (ite_runs_true h2 r)).mono (by omega) (by omega), natAbs_le (hS.abs_W _ _)⟩
    | false =>
      have hab : i / g ≠ i % g := by
        intro he
        have : isW g ((((c, x), (G.val, List.ofFn θ)), y), i) = true := by simp [isW, he]
        rw [h2] at this
        cases this
      have habF : (⟨i / g, ha⟩ : Fin g) ≠ ⟨i % g, hb⟩ := fun e => hab (congrArg Fin.val e)
      have hcap : Np.cap c (i / g) (i % g) = N.c ⟨i / g, ha⟩ ⟨i % g, hb⟩ := h.given.cap_eq ⟨i / g, ha⟩ ⟨i % g, hb⟩ habF
      cases h3 : isPsi K g ((((c, x), (G.val, List.ofFn θ)), y), i) with
      | false =>
        have hcolB : col K x (i % g) ≠ G.val := by
          intro he
          have : isPsi K g ((((c, x), (G.val, List.ofFn θ)), y), i) = true := by simp [isPsi, he]
          rw [h3] at this
          cases this
        have hl : (labOf K g Np.toPaperNetwork ((c, x), (G.val, List.ofFn θ)) (i / g) (i % g)).length = N.c ⟨i / g, ha⟩ ⟨i % g, hb⟩ :=
          (length_labOf h hβ hθ ham hb hcolB).trans hcap
        have ev : termVal K g Np.toPaperNetwork N.toPaperNetwork ((((c, x), (G.val, List.ofFn θ)), y), i) =
            N.toPaperNetwork.f ⟨i / g, ha⟩ ⟨i % g, hb⟩ (zA K g Np.toPaperNetwork (((c, x), (G.val, List.ofFn θ)), y) (i / g))
              (labOf K g Np.toPaperNetwork ((c, x), (G.val, List.ofFn θ)) (i / g) (i % g)) := by
          simp only [termVal, h1, h2, h3, if_false, Bool.false_eq_true]
          exact dif_pos ⟨ha, hb⟩
        rw [ev]
        refine ⟨?_, natAbs_le (hS.abs_f _ _ _ _)⟩
        rw [f_toPaperNetwork habF hl]
        have r := gate_runs h (u := ((((c, x), (G.val, List.ofFn θ)), y), i)) (q := qW K g Np.toPaperNetwork) (M := mapIn (qF K g Np.toPaperNetwork) Np.f) rfl hza le_rfl le_rfl
          fun hm => mapIn_runs (h.given.f_runs ⟨i / g, ha⟩ ⟨i % g, hb⟩ habF _ hm _ (mem_words.2 hl))
        exact (ite_runs_false h1 (ite_runs_false h2 (ite_runs_false h3 r))).mono (by omega) (by omega)
      | true =>
        have hcolB : col K x (i % g) = G.val := by simpa [isPsi] using h3
        have hbm : i % g ∈ members K g x G := mem_members.2 ⟨hb, hcolB⟩
        have hzb : (zA K g Np.toPaperNetwork (((c, x), (G.val, List.ofFn θ)), y) (i % g)).length = N.len ⟨i % g, hb⟩ :=
          (length_zA Np.toPaperNetwork hbm).trans (h.given.len_eq ⟨i % g, hb⟩)
        have ev : termVal K g Np.toPaperNetwork N.toPaperNetwork ((((c, x), (G.val, List.ofFn θ)), y), i) =
            N.toPaperNetwork.Ψ ⟨i / g, ha⟩ ⟨i % g, hb⟩ (zA K g Np.toPaperNetwork (((c, x), (G.val, List.ofFn θ)), y) (i / g))
              (zA K g Np.toPaperNetwork (((c, x), (G.val, List.ofFn θ)), y) (i % g)) := by
          rw [← sum_valF h.is ha hb, ← hcap]
          simp only [termVal, h1, h2, h3, if_true, if_false, Bool.false_eq_true, nLab]
          rfl
        rw [ev]
        refine ⟨?_, natAbs_le (hS.abs_Ψ _ _ _ _ habF)⟩
        rw [psi_toPaperNetwork h.is habF]
        have r := gate_runs h (u := ((((c, x), (G.val, List.ofFn θ)), y), i)) (q := qW K g Np.toPaperNetwork)
          (M := gated (mapIn (qMb K g Np) Np.mem) (mapIn (qPsi K g Np) Np.Ψ)) (t := 2 * τ + 1)
          (S' := size ((((c, x), (G.val, List.ofFn θ)), y), i) + S + 4) rfl hza (by omega) (by omega)
          fun hm => gate_runs h (q := qMb K g Np) (M := mapIn (qPsi K g Np) Np.Ψ) rfl hzb le_rfl le_rfl
            fun hm' => mapIn_runs (h.given.Ψ_runs ⟨i / g, ha⟩ ⟨i % g, hb⟩ habF _ hm _ hm')
        exact (ite_runs_false h1 (ite_runs_false h2 (ite_runs_true h3 r))).mono (by omega) (by omega)
end Eight.ViaGrouping.Table
