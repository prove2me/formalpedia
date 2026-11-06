-- Prove2me | solution 1 for Coding.padRow_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:46:14.776486+00:00
-- url     : https://prove2.me/submissions/954767de-4e05-4e3b-8c33-34263cd60429

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
import Theorems.Thm_Coding_heG_padRow
import Theorems.Thm_Coding_pieceRow_skip
import Theorems.Thm_Eight_block_ext
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Coding
open Finset Groundwork Groundwork.Prog Groundwork.Grid ClauseBound.Alg ClauseBound.Alg.GridNet Eight.SecNetworks Eight.ViaGrouping Eight.Level
variable {g : ℕ} {tr : Bool} {lam : ℕ}
namespace Coding
theorem _root_.solution (a : Fin (nParts g g tr)) {z z' : List Bool} (hz : z.length = g * ((g * g - 1) * lam)) (hz' : z'.length = g * ((g * g - 1) * lam))
    (h : padRow g tr lam a.val z = padRow g tr lam a.val z') : z = z' := by
  refine Code.block_ext ((g * g - 1) * lam) g z z' hz hz' fun x hx => ?_
  refine Code.block_ext lam (g * g - 1) _ _ (length_block_row hz hx) (length_block_row hz' hx) fun u' hu' => ?_
  have hnd := nodeG_lt' a hx
  have hu : (if u' < nodeG g tr a.val x then u' else u' + 1) < g * g := by split_ifs <;> omega
  rw [← pieceRow_skip (tr := tr) a.val z x u', ← pieceRow_skip (tr := tr) a.val z' x u', ← heG_padRow a hz hx hu, ← heG_padRow a hz' hx hu, h]
end Coding
