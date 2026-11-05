-- Prove2me | solution 1 for Eight.network_value_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:48:52.894198+00:00
-- url     : https://prove2.me/submissions/634e74c3-898b-4407-a194-e1b615543e09

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
import Theorems.Thm_Eight_continued_of_mem
import Theorems.Thm_Eight_continued_of_not_mem
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Count_le_mul_mu
import Theorems.Thm_Groundwork_Prog_Count_value_wordNet
import Theorems.Thm_Groundwork_SatNet_exists_model
import Theorems.Thm_Groundwork_SatNet_good_toState
import Theorems.Thm_Groundwork_SatNet_toState_inj
import Theorems.Thm_Groundwork_SatNet_value_eq_card_good
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
namespace Eight
theorem _root_.solution {g : ℕ} (hg : 0 < g) (Φ : Formula) (h3 : ∀ C ∈ Φ, C.length ≤ 3) : (networkOf g Φ).value = numSat Φ := by
  have hm := Count.le_mul_mu hg Φ
  rw [Count.value_wordNet hg, value_eq_card_good]
  congr 1
  symm
  have hmod : ∀ a : Assignment Φ, Satisfies Φ a → IsModel Φ (continued a) := by
    intro a ha
    refine ⟨fun C hC => ?_, fun v hv => continued_of_not_mem a fun h => ?_⟩
    · obtain ⟨l, hl, h, e⟩ := ha C hC
      exact ⟨l, hl, by rw [continued_of_mem a h, e]⟩
    · obtain ⟨C, hC, l, hl, e⟩ := mem_occurring.1 h
      exact hv C hC l hl e
  refine Finset.card_bij (fun a _ => toState Φ (continued a)) ?_ ?_ ?_
  · intro a ha
    simpa using good_toState h3 (hmod a (Finset.mem_filter.1 ha).2)
  · intro a ha a' ha' h
    have := toState_inj h3 hm (hmod a (Finset.mem_filter.1 ha).2) (hmod a' (Finset.mem_filter.1 ha').2) h
    funext v
    have h2 := congrFun this v.1
    rwa [continued_of_mem a v.2, continued_of_mem a' v.2] at h2
  · intro z hz
    obtain ⟨a, ha, rfl⟩ := exists_model hm (Finset.mem_filter.1 hz).2
    have he : continued (Φ := Φ) (fun v => a v.1) = a := by
      funext v
      by_cases h : v ∈ occurring Φ
      · exact continued_of_mem _ h
      · rw [continued_of_not_mem _ h]
        exact (ha.2 v fun C hC l hl e => h (mem_occurring.2 ⟨C, hC, l, hl, e⟩)).symm
    refine ⟨fun v => a v.1, ?_, by rw [he]⟩
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun C hC => ?_⟩
    obtain ⟨l, hl, e⟩ := ha.1 C hC
    exact ⟨l, hl, mem_occurring.2 ⟨C, hC, l, hl, rfl⟩, e⟩
end Eight
