-- Prove2me | solution 1 for Eight.SecNetworks.card_pairs_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:20:52.07755+00:00
-- url     : https://prove2.me/submissions/6ab4c90d-96d3-44cb-8d91-111aed5e0cc9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecNetworks_Defs
import Definitions.Def_Groundwork_Net_Colouring
import Definitions.Def_Groundwork_Net_Colouring
import Definitions.Def_Eight_SecNetworks_Grouping
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_all
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
open Finset Groundwork.Colouring
variable {g K : ℕ}
namespace Eight.SecNetworks
theorem _root_.solution (hK : 1 ≤ K) : 2 * #{p : Fin K × Fin K | p.1 < p.2} < K ^ 2 := by
  have hswap : #{p : Fin K × Fin K | p.2 < p.1} = #{p : Fin K × Fin K | p.1 < p.2} := by
    refine card_bij (fun p _ => p.swap) ?_ ?_ ?_
    · intro p hp; simpa using hp
    · intro p _ q _ h; exact Prod.swap_injective h
    · intro p hp; exact ⟨p.swap, by simpa using hp, by simp⟩
  have hdiag : #{p : Fin K × Fin K | p.1 = p.2} = K := by
    have h := card_bij (s := (univ : Finset (Fin K))) (t := ({p : Fin K × Fin K | p.1 = p.2} : Finset (Fin K × Fin K))) (fun a _ => (a, a)) (by simp)
      (fun a _ b _ h => (Prod.mk.inj h).1) (fun p hp => ⟨p.1, mem_univ _, Prod.ext rfl (mem_filter.1 hp).2⟩)
    simpa using h.symm
  have hall : #{p : Fin K × Fin K | p.1 < p.2} + #{p : Fin K × Fin K | p.2 < p.1} + #{p : Fin K × Fin K | p.1 = p.2} = K ^ 2 := by
    rw [← card_union_of_disjoint, ← card_union_of_disjoint]
    · have : (({p : Fin K × Fin K | p.1 < p.2} : Finset (Fin K × Fin K)) ∪ ({p : Fin K × Fin K | p.2 < p.1} : Finset (Fin K × Fin K))) ∪ ({p : Fin K × Fin K | p.1 = p.2} : Finset (Fin K × Fin K)) = univ := by
        ext p
        simp only [mem_union, mem_filter, mem_univ, true_and, iff_true]
        rcases lt_trichotomy p.1 p.2 with h | h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
        · exact Or.inl (Or.inr h)
      rw [this]; simp [sq]
    · rw [disjoint_left]
      intro p hp hq
      simp only [mem_union, mem_filter, mem_univ, true_and] at hp hq
      rcases hp with h | h <;> exact absurd hq (by first | exact h.ne | exact h.ne')
    · rw [disjoint_left]
      intro p hp hq
      simp only [mem_filter, mem_univ, true_and] at hp hq
      exact absurd hq (not_lt.2 hp.le)
  omega
end Eight.SecNetworks
