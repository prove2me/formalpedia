-- Prove2me | solution 1 for Coding.length_pieceRow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:00:09.563406+00:00
-- url     : https://prove2.me/submissions/1f8af23d-8b2d-4649-9b4d-75900ec9d88c

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
import Theorems.Thm_P2M_Coding_nodeG_lt__a7e270dc1ce1
import Theorems.Thm_Coding_length_block_row
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_length_block
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Coding
open Finset Groundwork Groundwork.Prog Groundwork.Grid ClauseBound.Alg ClauseBound.Alg.GridNet Eight.SecNetworks Eight.ViaGrouping Eight.Level
variable {g : ℕ} {tr : Bool} {lam : ℕ}
namespace Coding
theorem _root_.solution (a : Fin (nParts g g tr)) {z : List Bool} (hz : z.length = g * ((g * g - 1) * lam)) {x u : ℕ} (hx : x < g) (hu : u < g * g) : (pieceRow g tr lam a.val z x u).length = lam := by
  have hnd := nodeG_lt' a hx
  unfold pieceRow
  by_cases h : u = nodeG g tr a.val x
  · rw [if_pos h, List.length_replicate]
  · rw [if_neg h]
    refine length_block ?_
    rw [length_block_row hz hx]
    refine Nat.mul_le_mul_right _ ?_
    split_ifs <;> omega
end Coding
