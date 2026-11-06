-- Prove2me | solution 1 for Coding.pieceRow_skip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:37:57.052652+00:00
-- url     : https://prove2.me/submissions/e0a0a288-d644-4cfc-8367-22f797483976

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
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Coding
open Finset Groundwork Groundwork.Prog Groundwork.Grid ClauseBound.Alg ClauseBound.Alg.GridNet Eight.SecNetworks Eight.ViaGrouping Eight.Level
variable {g : ℕ} {tr : Bool} {lam : ℕ}
namespace Coding
theorem _root_.solution (a : ℕ) (z : List Bool) (x u' : ℕ) : pieceRow g tr lam a z x (if u' < nodeG g tr a x then u' else u' + 1) = block lam u' (block ((g * g - 1) * lam) x z) := by
  unfold pieceRow
  by_cases hlt : u' < nodeG g tr a x
  · rw [if_pos hlt, if_neg (by omega), if_pos hlt]
  · rw [if_neg hlt, if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel]
end Coding
