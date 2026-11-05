-- Prove2me | solution 1 for Eight.SecNetworks.groupedTables_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:53:50.926718+00:00
-- url     : https://prove2.me/submissions/7089a313-3879-4806-a74d-0731ed15634d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecNetworks_LemGrouping
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_NetVal
import Mathlib.Tactic
import Definitions.Def_Eight_SecNetworks_Tables
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_filter
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
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.filter
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
theorem _root_.solution (Np : NetworkProcedures C) (c : C) (N : Paper.Network (Fin g) (List Bool) (List Bool)) (hK0 : 0 < K) (x L : ℕ) (γ : Fin K) (Θ : Fin K → List Bool)
    (hΘ : ∀ γ', γ' ≠ γ → (Θ γ').length = L) :
    groupedTables Np c N hK0 x L γ Θ =
      (if ∀ γ', γ' ≠ γ → ∀ bit ∈ appendedBits (g := g) Np c x γ γ' (Θ γ'), bit = false then 1 else 0) *
        ∑ z ∈ tuples (fun a => grouping hK0 x a = γ) N.S [],
          (∏ a with grouping hK0 x a = γ, N.W a (z a)) *
            (∏ p ∈ pairs (Fin g) with grouping hK0 x p.1 = γ ∧ grouping hK0 x p.2 = γ, N.Ψ p.1 p.2 (z p.1) (z p.2)) *
            ∏ p : Fin g × Fin g with grouping hK0 x p.1 = γ ∧ grouping hK0 x p.2 ≠ γ, N.f p.1 p.2 (z p.1) (thetaAt Np c hK0 x Θ p.1 p.2) := by
  have hcond : (∀ b ∈ univ.erase γ, Θ b ∈ mD K g Np c x L (min γ b) (max γ b)) ↔
      ∀ γ', γ' ≠ γ → ∀ bit ∈ appendedBits (g := g) Np c x γ γ' (Θ γ'), bit = false := by
    refine forall_congr' fun b => ?_
    simp only [mem_erase, mem_univ, and_true]
    refine imp_congr_right fun hb => ?_
    simp [mD, appendedBits, hΘ b hb]
  have hprod : ∀ z : Fin g → List Bool,
      ∏ b ∈ univ.erase γ, ∏ p : Fin g × Fin g with grouping hK0 x p.1 = γ ∧ grouping hK0 x p.2 = b,
        N.f p.1 p.2 (z p.1) (mdec K g Np c x (min γ b) (max γ b) (Θ b) (if γ < b then p else p.swap))
      = ∏ p : Fin g × Fin g with grouping hK0 x p.1 = γ ∧ grouping hK0 x p.2 ≠ γ, N.f p.1 p.2 (z p.1) (thetaAt Np c hK0 x Θ p.1 p.2) := by
    intro z
    rw [← prod_fiberwise_of_maps_to (s := univ.filter fun p : Fin g × Fin g => grouping hK0 x p.1 = γ ∧ grouping hK0 x p.2 ≠ γ) (t := univ.erase γ)
      (g := fun p => grouping hK0 x p.2) (fun p hp => by simpa using (mem_filter.1 hp).2.2)]
    refine prod_congr rfl fun b hb => ?_
    have hb' : b ≠ γ := by simpa using hb
    rw [filter_filter]
    refine prod_congr (filter_congr fun p _ => ?_) fun p hp => ?_
    · constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, h2 ▸ hb'⟩, h2⟩
      · rintro ⟨⟨h1, _⟩, h2⟩
        exact ⟨h1, h2⟩
    · obtain ⟨⟨h1, _⟩, h2⟩ := (mem_filter.1 hp).2
      unfold thetaAt
      rw [h1, h2]
      rfl
  change ∑ z ∈ tuples (fun a => grouping hK0 x a = γ) N.S [],
      ((∏ a with grouping hK0 x a = γ, N.W a (z a)) * ∏ p ∈ pairs (Fin g) with grouping hK0 x p.1 = γ ∧ grouping hK0 x p.2 = γ, N.Ψ p.1 p.2 (z p.1) (z p.2)) *
        ∏ b ∈ univ.erase γ, (if Θ b ∈ mD K g Np c x L (min γ b) (max γ b) then
          ∏ p : Fin g × Fin g with grouping hK0 x p.1 = γ ∧ grouping hK0 x p.2 = b,
            N.f p.1 p.2 (z p.1) (mdec K g Np c x (min γ b) (max γ b) (Θ b) (if γ < b then p else p.swap)) else 0) = _
  rw [mul_sum]
  refine sum_congr rfl fun z _ => ?_
  rw [prod_ite_zero, hprod]
  simp only [hcond]
  split_ifs <;> ring
end Eight.SecNetworks
