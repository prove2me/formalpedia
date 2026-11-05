-- Prove2me | solution 1 for Eight.SecNetworks.tables_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:57:42.864205+00:00
-- url     : https://prove2.me/submissions/7baff71c-4d7b-44a2-91ec-f6a56a5d85c4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecNetworks_LemGrouping
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_NetVal
import Mathlib.Tactic
import Definitions.Def_Eight_SecNetworks_Tables
import Theorems.Thm_Eight_SecNetworks_groupedTables_eq
import Theorems.Thm_Eight_SecNetworks_length_thetaAt
import Theorems.Thm_Eight_SecNetworks_Net_sized_toPaperNetwork
import Theorems.Thm_Eight_SecNetworks_presents_toPaperNetwork
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_Network_merge_c
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_congr
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
import Theorems.Thm_Groundwork_mem_tuples
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
import Theorems.Thm_P2M_Eight_SecNetworks_Net___toPaperNetwork_89d84f9cfc58
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
open Eight Eight.SecNetworks
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Paper
variable {C : Type} {g K : ℕ}
namespace Eight.SecNetworks
theorem _root_.solution [HasSize C] {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ} (h : IsNetwork Np c N P B τ S) (hK0 : 0 < K) (x L : ℕ)
    (hL : ∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (grouping hK0 x) γ γ' ≤ L) (γ : Fin K) (Θ : Fin K → List Bool) (hΘ : ∀ γ', γ' ≠ γ → (Θ γ').length = L) :
    groupedTables Np.toPaperNetwork c N.toPaperNetwork hK0 x L γ Θ =
      (if ∀ γ', γ' ≠ γ → ∀ bit ∈ appendedBits (g := g) Np.toPaperNetwork c x γ γ' (Θ γ'), bit = false then 1 else 0) *
        ∑ z ∈ tuples (fun a => grouping hK0 x a = γ) N.S [],
          (∏ a with grouping hK0 x a = γ, N.W a (z a)) *
            (∏ p ∈ pairs (Fin g) with grouping hK0 x p.1 = γ ∧ grouping hK0 x p.2 = γ, N.Ψ p.1 p.2 (z p.1) (z p.2)) *
            ∏ p : Fin g × Fin g with grouping hK0 x p.1 = γ ∧ grouping hK0 x p.2 ≠ γ, N.f p.1 p.2 (z p.1) (thetaAt Np.toPaperNetwork c hK0 x Θ p.1 p.2) := by
  have hN : Paper.IsNetwork Np.toPaperNetwork c N.toPaperNetwork P B _ _ := ⟨Net.sized_toPaperNetwork h.is, presents_toPaperNetwork h⟩
  have hL' : ∀ γ γ' : Fin K, γ ≠ γ' → (N.toPaperNetwork.merge (grouping hK0 x) [] []).c γ γ' ≤ L := fun γ γ' hne => by
    rw [Groundwork.Network.merge_c]
    exact hL γ γ' hne
  rw [groupedTables_eq Np.toPaperNetwork c N.toPaperNetwork hK0 x L γ Θ hΘ]
  congr 1
  symm
  refine sum_subset_zero_on_sdiff (fun z hz => ?_) (fun z hz => ?_) fun z hz => ?_
  · rw [mem_tuples] at hz ⊢
    exact fun a => ⟨fun ha => mem_words.2 (h.is.len_S a _ ((hz a).1 ha)), (hz a).2⟩
  · obtain ⟨hz1, hz2⟩ := mem_sdiff.1 hz
    rw [mem_tuples] at hz1 hz2
    obtain ⟨a, ha, hza⟩ : ∃ a, grouping hK0 x a = γ ∧ z a ∉ N.S a := by
      by_contra hcon
      exact hz2 fun a => ⟨fun ha => by_contra fun hza => hcon ⟨a, ha, hza⟩, (hz1 a).2⟩
    rw [prod_eq_zero (i := a) (mem_filter.2 ⟨mem_univ _, ha⟩) (by simp only [Net.toPaperNetwork]; rw [if_neg hza]), zero_mul, zero_mul]
  · rw [mem_tuples] at hz
    congr 1
    · congr 1
      · refine prod_congr rfl fun a ha => ?_
        simp only [Net.toPaperNetwork]
        rw [if_pos ((hz a).1 (mem_filter.1 ha).2)]
      · refine prod_congr rfl fun p hp => ?_
        obtain ⟨hp1, hp2, hp3⟩ := mem_filter.1 hp
        have hlt : p.1 < p.2 := (mem_filter.1 hp1).2
        exact (Net.Ψ_toPaperNetwork h.is hlt.ne ((hz _).1 hp2) ((hz _).1 hp3)).symm
    · refine prod_congr rfl fun p hp => ?_
      obtain ⟨hp1, hp2⟩ := (mem_filter.1 hp).2
      have hne : grouping hK0 x p.1 ≠ grouping hK0 x p.2 := fun e => hp2 (e ▸ hp1)
      have hlen := length_thetaAt Np.toPaperNetwork hK0 hN x L hL' Θ hne (hΘ _ hp2)
      simp only [Net.toPaperNetwork] at hlen ⊢
      rw [if_pos ⟨fun e => hne (e ▸ rfl), (hz _).1 hp1, mem_words.2 hlen⟩]
end Eight.SecNetworks
