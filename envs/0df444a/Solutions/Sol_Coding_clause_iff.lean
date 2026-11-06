-- Prove2me | solution 1 for Coding.clause_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:40:15.146592+00:00
-- url     : https://prove2.me/submissions/e6201c0d-9a8c-41e8-aebb-ba1e6390e498

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_OccLinks
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_Eight_ViaGrouping_SatPsi
import Mathlib.Tactic.Ring
import Definitions.Def_Coding_Occ
import Theorems.Thm_Coding_getD_padOcc
import Theorems.Thm_Coding_length_getD_le
import Theorems.Thm_Coding_litAt_eq
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_any
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_snd
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
attribute [local fun_prop] Groundwork.PolyT.any
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.snd
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
theorem _root_.solution (h3 : ∀ C ∈ Φ, C.length ≤ 3) (a : Fin g) (z : List Bool) {c : ℕ} (hc : c < mu g Φ) :
    ((List.range 3).any fun j => (litAt 3 Φ ((a.val * mu g Φ + c) * 3 + j)).map Prod.snd == some ((padOcc g Φ a z).getD (c * 3 + j) false)) = true ↔
      ((List.range (Φ.getD (a.val * mu g Φ + c) []).length).any fun j => isTrue g Φ a.val z (a.val * mu g Φ + c, j)) = true := by
  have h5 := length_getD_le h3 (a.val * mu g Φ + c)
  have key : ∀ j < 3, ((litAt 3 Φ ((a.val * mu g Φ + c) * 3 + j)).map Prod.snd = some ((padOcc g Φ a z).getD (c * 3 + j) false) ↔
      j < (Φ.getD (a.val * mu g Φ + c) []).length ∧ isTrue g Φ a.val z (a.val * mu g Φ + c, j) = true) := by
    intro j hj
    have e1 : ((a.val * mu g Φ + c) * 3 + j) / 3 = a.val * mu g Φ + c := by omega
    have e2 : ((a.val * mu g Φ + c) * 3 + j) % 3 = j := by omega
    have e3 : (c * 3 + j) / 3 = c := by omega
    have e4 : (c * 3 + j) % 3 = j := by omega
    rw [litAt_eq, e1, e2, getD_padOcc a z (by omega), e3, e4]
    by_cases h : j < (Φ.getD (a.val * mu g Φ + c) []).length
    · rw [if_pos h, decide_eq_true h, Bool.true_and, Option.map_some, Option.some.injEq]
      unfold isTrue
      rw [beq_iff_eq]
      exact ⟨fun e => ⟨h, e.symm⟩, fun e => e.2.symm⟩
    · rw [if_neg h]
      exact ⟨fun e => by simp at e, fun e => absurd e.1 h⟩
  simp only [List.any_eq_true, List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨j, hj, h⟩
    exact ⟨j, (key j hj).1 h⟩
  · rintro ⟨j, hj, h⟩
    exact ⟨j, by omega, (key j (by omega)).2 ⟨hj, h⟩⟩
end Coding
