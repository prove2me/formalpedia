-- Prove2me | solution 1 for CountKSat.Value.value_net_eq_cntN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:05:51.144727+00:00
-- url     : https://prove2.me/submissions/d700295f-f3da-475c-aa7d-e833c1aa23de

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_CountKSat_Value
import Theorems.Thm_CountKSat_Value_ext_val
import Theorems.Thm_CountKSat_Value_ext_of_le
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_length
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
open Finset Groundwork Groundwork.Prog Groundwork.SatNet
open CountKSat.Value
namespace CountKSat.Value
theorem _root_.solution {g μ k n : ℕ} {x : Fml} (hk : ∀ C ∈ x, C.length ≤ k) (hm : x.length ≤ g * μ)
    (hlt : ∀ C ∈ x, ∀ l ∈ C, l.1 < n) (hocc : ∀ i < n, ∃ C ∈ x, ∃ l ∈ C, l.1 = i) :
    (net x g μ k).value = cntN n x := by
  rw [value_eq_card_good]
  congr 1
  symm
  have hmod : ∀ a : Fin n → Bool, (∀ C ∈ x, ∃ l ∈ C, ext a l.1 = l.2) → IsModel x (ext a) := by
    intro a ha
    refine ⟨ha, fun v hv => ?_⟩
    by_cases h : v < n
    · obtain ⟨C, hC, l, hl, rfl⟩ := hocc v h
      exact absurd rfl (hv C hC l hl)
    · exact ext_of_le a (Nat.not_lt.1 h)
  refine Finset.card_bij (fun a _ => toState x (ext a)) ?_ ?_ ?_
  · intro a ha
    simpa using good_toState hk (hmod a (Finset.mem_filter.1 ha).2)
  · intro a ha a' ha' h
    have := toState_inj hk hm (hmod a (Finset.mem_filter.1 ha).2) (hmod a' (Finset.mem_filter.1 ha').2) h
    funext i
    have h2 := congrFun this i.val
    rwa [ext_val, ext_val] at h2
  · intro z hz
    obtain ⟨a, ha, rfl⟩ := exists_model hm (Finset.mem_filter.1 hz).2
    have he : ext (fun i : Fin n => a i.val) = a := by
      funext v
      by_cases h : v < n
      · exact ext_val (fun i : Fin n => a i.val) ⟨v, h⟩
      · rw [ext_of_le _ (Nat.not_lt.1 h)]
        exact (ha.2 v fun C hC l hl e => h (e ▸ hlt C hC l hl)).symm
    exact ⟨fun i => a i.val, by simpa [he] using ha.1, by rw [he]⟩
end CountKSat.Value
