-- Prove2me | solution 1 for Coding.heG_padRow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:15:34.464589+00:00
-- url     : https://prove2.me/submissions/e5faa14a-b08f-4b28-b8e9-aaf939ddc5b3

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
import Theorems.Thm_Coding_block_flatMap_range
import Theorems.Thm_Coding_padRow_eq
import Theorems.Thm_Coding_length_pieceRow
import Theorems.Thm_Coding_length_rowPart
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
theorem _root_.solution (a : Fin (nParts g g tr)) {z : List Bool} (hz : z.length = g * ((g * g - 1) * lam)) {x u : ℕ} (hx : x < g) (hu : u < g * g) :
    heG g g lam (padRow g tr lam a.val z) x u = pieceRow g tr lam a.val z x u := by
  rw [heG, padRow_eq, block_flatMap_range g (g * g * lam) _ (fun _ hx => length_rowPart a hz hx) hx, block_flatMap_range (g * g) lam _ (fun _ hu => length_pieceRow a hz hx hu) hu]
end Coding
