-- Prove2me | solution 1 for Coding.stOccNet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:22:48.770198+00:00
-- url     : https://prove2.me/submissions/77e22da8-f916-4044-b356-15b773843053

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_OccLinks
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_Eight_ViaGrouping_SatPsi
import Mathlib.Tactic.Ring
import Definitions.Def_Coding_Occ
import Theorems.Thm_Coding_length_padOcc
import Theorems.Thm_Coding_zero_padOcc
import Theorems.Thm_Coding_exists_padOcc
import Theorems.Thm_Coding_padOcc_inj
import Theorems.Thm_Coding_clauses_iff
import Theorems.Thm_Coding_inside_iff
import Theorems.Thm_Coding_restr_padOcc
import Theorems.Thm_Coding_capF_eq
import Theorems.Thm_Eight_ViaGrouping_satF_eq
import Theorems.Thm_Eight_ViaGrouping_satPsi_eq
import Theorems.Thm_Groundwork_Grid_boole_congr
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_Prog_Count_boole_congr
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
open Coding
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight.SecNetworks Eight.ViaGrouping
variable {g : ℕ} {Φ : Fml}
namespace Coding
theorem _root_.solution : StOccNet := by
  intro g Φ hg h3
  refine ⟨fun a z _ => ?_, fun a z hz z' hz' h => ?_, fun a y hy hno => ?_, fun a z _ => ?_, fun a b hab z _ z' _ => ?_, fun a b _ => ?_, fun a b hab z _ θ hθ => ?_⟩
  · exact mem_words.2 (length_padOcc a z)
  · exact padOcc_inj h3 a (mem_words.1 hz) (mem_words.1 hz') h
  · change wF g 3 (Φ, (a.val, y)) = 0
    unfold wF
    rw [if_neg]
    intro hc
    simp only [Bool.and_eq_true] at hc
    obtain ⟨z, hz, hzy⟩ := exists_padOcc hg a (mem_words.1 hy) hc.1.1
    exact hno z (mem_words.2 hz) hzy
  · change wF g 3 (Φ, (a.val, padOcc g Φ a z)) = _
    unfold wF occNet
    refine boole_congr ?_
    simp only [Bool.and_eq_true]
    exact ⟨fun h => ⟨(clauses_iff hg h3 a z).1 h.1.2, (inside_iff hg h3 a z).1 h.2⟩, fun h => ⟨⟨zero_padOcc hg a z, (clauses_iff hg h3 a z).2 h.1⟩, (inside_iff hg h3 a z).2 h.2⟩⟩
  · change (wordNet g 3 Φ).Ψ a b (padOcc g Φ a z) (padOcc g Φ b z') = if restrict g Φ a.val b.val z = restrict g Φ b.val a.val z' then 1 else 0
    rw [← satPsi_eq hab, satPsi]
    change (if restr g 3 Φ a.val b.val (padOcc g Φ a z) = restr g 3 Φ b.val a.val (padOcc g Φ b z') then (1 : ℤ) else 0) = _
    rw [restr_padOcc hg h3 hab, restr_padOcc hg h3 hab.symm]
  · exact capF_eq hg h3 a.val b.val
  · change fF g 3 (Φ, ((a.val, b.val), (padOcc g Φ a z, θ))) = if restrict g Φ a.val b.val z = θ then 1 else 0
    rw [satF_eq a.val b.val _ ((mem_words.1 hθ).trans (capF_eq hg h3 a.val b.val).symm), restr_padOcc hg h3 hab]
end Coding
