-- Prove2me | solution 1 for Coding.exists_padRow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:38:06.76419+00:00
-- url     : https://prove2.me/submissions/9ffccb75-b427-4dc1-8c78-f993f6c4d92f

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
import Theorems.Thm_Coding_length_flatMap_range
import Theorems.Thm_Coding_block_flatMap_range
import Theorems.Thm_P2M_Coding_nodeG_lt__a7e270dc1ce1
import Theorems.Thm_Coding_length_padRow
import Theorems.Thm_Coding_heG_padRow
import Theorems.Thm_Eight_block_ext
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_length_block
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Coding
open Finset Groundwork Groundwork.Prog Groundwork.Grid ClauseBound.Alg ClauseBound.Alg.GridNet Eight.SecNetworks Eight.ViaGrouping Eight.Level
variable {g : ℕ} {tr : Bool} {lam : ℕ}
namespace Coding
theorem _root_.solution (a : Fin (nParts g g tr)) {y : List Bool} (hy : y.length = g * (g * g * lam)) (h0 : ∀ x < g, heG g g lam y x (nodeG g tr a.val x) = List.replicate lam false) :
    ∃ z : List Bool, z.length = g * ((g * g - 1) * lam) ∧ padRow g tr lam a.val z = y := by
  have hrow : ∀ x < g, (block (g * g * lam) x y).length = g * g * lam := fun x hx => length_block (by rw [hy]; exact Nat.mul_le_mul_right _ hx)
  have hlen : ∀ x < g, ∀ u < g * g, (heG g g lam y x u).length = lam := fun x hx u hu => length_block (by rw [hrow x hx]; exact Nat.mul_le_mul_right _ hu)
  have hskip : ∀ x < g, ∀ u' < g * g - 1, (heG g g lam y x (if u' < nodeG g tr a.val x then u' else u' + 1)).length = lam := fun x hx u' hu' => hlen x hx _ (by split_ifs <;> omega)
  have hpart : ∀ x < g, ((List.range (g * g - 1)).flatMap fun u' => heG g g lam y x (if u' < nodeG g tr a.val x then u' else u' + 1)).length = (g * g - 1) * lam :=
    fun x hx => length_flatMap_range _ _ _ (hskip x hx)
  have hz : ((List.range g).flatMap fun x => (List.range (g * g - 1)).flatMap fun u' => heG g g lam y x (if u' < nodeG g tr a.val x then u' else u' + 1)).length = g * ((g * g - 1) * lam) :=
    length_flatMap_range _ _ _ hpart
  refine ⟨_, hz, Code.block_ext (g * g * lam) g _ _ (length_padRow a hz) hy fun x hx => ?_⟩
  have hl : (block (g * g * lam) x (padRow g tr lam a.val _)).length = g * g * lam := length_block (by rw [length_padRow a hz]; exact Nat.mul_le_mul_right _ hx)
  refine Code.block_ext lam (g * g) _ _ hl (hrow x hx) fun u hu => ?_
  have hnd := nodeG_lt' a hx
  change heG g g lam (padRow g tr lam a.val _) x u = heG g g lam y x u
  rw [heG_padRow a hz hx hu]
  unfold pieceRow
  by_cases hu0 : u = nodeG g tr a.val x
  · rw [if_pos hu0, hu0, h0 x hx]
  · have hu' : (if u < nodeG g tr a.val x then u else u - 1) < g * g - 1 := by split_ifs <;> omega
    have e : (if (if u < nodeG g tr a.val x then u else u - 1) < nodeG g tr a.val x then (if u < nodeG g tr a.val x then u else u - 1) else (if u < nodeG g tr a.val x then u else u - 1) + 1) = u := by
      split_ifs <;> omega
    rw [if_neg hu0, block_flatMap_range g _ _ hpart hx, block_flatMap_range (g * g - 1) lam _ (hskip x hx) hu', e]
end Coding
