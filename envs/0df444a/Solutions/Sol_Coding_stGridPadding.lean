-- Prove2me | solution 1 for Coding.stGridPadding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:55:39.397053+00:00
-- url     : https://prove2.me/submissions/374b31ab-3e62-4fef-9d16-daa3246ad675

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_GridDefs
import Definitions.Def_Coding_OccLists
import Definitions.Def_StepMachines_Math_CodeMore
import Definitions.Def_StepMachines_Math_CodeMore
import Definitions.Def_PaddedDescent_F_Table
import Definitions.Def_Eight_SecLevel_GridWords
import Mathlib.Tactic.Ring
import Definitions.Def_Coding_Grid
import Theorems.Thm_Coding_nMemb_self
import Theorems.Thm_P2M_Coding_nodeG_lt__a7e270dc1ce1
import Theorems.Thm_Coding_length_padRow
import Theorems.Thm_Coding_padRow_inj
import Theorems.Thm_Coding_exists_padRow
import Theorems.Thm_Coding_eq_replicate_of_bitsOf
import Theorems.Thm_Coding_W_eq_zero
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_length_block
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_P2M_Eight_Level_netOf__S_6e5e490549e4
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open Coding
open Finset Groundwork Groundwork.Prog Groundwork.Grid ClauseBound.Alg ClauseBound.Alg.GridNet Eight.SecNetworks Eight.ViaGrouping Eight.Level
variable {g : ℕ} {tr : Bool} {lam : ℕ}
namespace Coding
theorem _root_.solution : StGridPadding := by
  intro g tr lam yι Rm
  have e1 : g * (g ^ 2 - 1) * lam = g * ((g * g - 1) * lam) := by rw [pow_two, Nat.mul_assoc]
  have e2 : g ^ 3 * lam = g * (g * g * lam) := by ring
  refine ⟨fun a z hz => ?_, fun a z hz z' hz' h => ?_, fun a y hy hno => ?_, fun _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩
  · change padRow g tr lam a.val z ∈ (netOfι g tr lam yι Rm).S a
    rw [Eight.Level.netOfι_S, mem_words, e2]
    exact length_padRow a ((mem_words.1 hz).trans e1)
  · exact padRow_inj a ((mem_words.1 hz).trans e1) ((mem_words.1 hz').trans e1) h
  · have hy' : y ∈ (netOfι g tr lam yι Rm).S a := hy
    rw [Eight.Level.netOfι_S, mem_words, e2] at hy'
    by_contra hW
    have hrow : ∀ x < g, (block (g * g * lam) x y).length = g * g * lam := fun x hx => length_block (by rw [hy']; exact Nat.mul_le_mul_right _ hx)
    obtain ⟨z, hz, hzy⟩ := exists_padRow a hy' fun x hx => by
      refine eq_replicate_of_bitsOf (length_block (by rw [hrow x hx]; exact Nat.mul_le_mul_right _ (nodeG_lt' a hx))) ?_
      by_contra hne
      exact hW (W_eq_zero yι Rm a y ⟨x, by rw [nMemb_self]; exact hx⟩ hne)
    exact hno z (mem_words.2 (hz.trans e1.symm)) hzy
end Coding
