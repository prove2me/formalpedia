-- Prove2me | solution 1 for Eight.card_first_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:52:45.490207+00:00
-- url     : https://prove2.me/submissions/c5872b2e-e108-424f-80a4-21b13a502a54

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecProof_NetworkDefs
import Definitions.Def_SingleBitPieces_SecProof_Cost
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Count
import Mathlib.Tactic
import Definitions.Def_Eight_SecProof_Network
import Theorems.Thm_Eight_mem_occurring
import Theorems.Thm_Eight_mem_occurrencesOf
import Theorems.Thm_Eight_exists_link_of_earlier
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_SatNet_exists_slot
import Theorems.Thm_Groundwork_SatNet_idx_injective
import Theorems.Thm_Groundwork_SatNet_lit_mem
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
open Eight
open Finset Groundwork Groundwork.Prog Groundwork.SatNet Paper
variable {Φ : Formula} {g μ k : ℕ}
namespace Eight
theorem _root_.solution (hk : ∀ C ∈ Φ, C.length ≤ k) (hm : Φ.length ≤ g * μ) : #{q ∈ occurrencesOf Φ g μ k | ¬ ∃ p, Link Φ p q} = #(occurring Φ) := by
  have hlab : ∀ q ∈ occurrencesOf Φ g μ k, ∃ l, lit Φ q = some l ∧ lab Φ q = some l.1 := by
    intro q hq
    obtain ⟨l, hl⟩ := Option.ne_none_iff_exists'.1 (mem_occurrencesOf.1 hq)
    exact ⟨l, hl, by simp [lab, hl]⟩
  refine Finset.card_bij (fun q _ => (lab Φ q).getD 0) ?_ ?_ ?_
  · intro q hq
    obtain ⟨l, hl, hv⟩ := hlab q (Finset.mem_filter.1 hq).1
    obtain ⟨C, hC, hlC⟩ := lit_mem hl
    simp only [hv, Option.getD_some]
    exact mem_occurring.2 ⟨C, hC, l, hlC, rfl⟩
  · intro q hq q' hq' e
    obtain ⟨l, -, hv⟩ := hlab q (Finset.mem_filter.1 hq).1
    obtain ⟨l', -, hv'⟩ := hlab q' (Finset.mem_filter.1 hq').1
    simp only [hv, hv', Option.getD_some] at e
    have hqq : lab Φ q = lab Φ q' := by rw [hv, hv', e]
    rcases lt_trichotomy (idx q) (idx q') with h | h | h
    · exact absurd (exists_link_of_earlier h hqq (by simp [hv'])) (Finset.mem_filter.1 hq').2
    · exact idx_injective h
    · exact absurd (exists_link_of_earlier h hqq.symm (by simp [hv])) (Finset.mem_filter.1 hq).2
  · intro v hv
    obtain ⟨C, hC, l, hl, rfl⟩ := mem_occurring.1 hv
    obtain ⟨p₀, hp₀⟩ := exists_slot (g := g) (μ := μ) hk hm hC hl
    obtain ⟨q, hq, hmin⟩ := Finset.exists_min_image ({r : Slot g μ k | lab Φ r = some l.1} : Finset (Slot g μ k)) idx
      ⟨p₀, Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [lab, hp₀]; rfl⟩⟩
    have hq' : lab Φ q = some l.1 := by simpa using hq
    refine ⟨q, Finset.mem_filter.2 ⟨mem_occurrencesOf.2 fun h => ?_, ?_⟩, by simp [hq']⟩
    · simp [lab, h] at hq'
    · rintro ⟨p, hp⟩
      have := hmin p (by simp [hp.2.2.1, hq'])
      have := hp.1
      omega
end Eight
