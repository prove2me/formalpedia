-- Prove2me | solution 1 for Coding.eq_replicate_of_bitsOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:38:08.140945+00:00
-- url     : https://prove2.me/submissions/4b3d41f0-156c-440a-aa7e-c6628fdfda4d

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
import Theorems.Thm_Coding_ext_getD
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
theorem _root_.solution {w : List Bool} (hw : w.length = lam) (h : Grid.bitsOf lam w = fun _ => false) : w = List.replicate lam false := by
  refine ext_getD (by rw [hw, List.length_replicate]) fun i hi => ?_
  have h1 : w.getD i false = false := congrFun h ⟨i, hw ▸ hi⟩
  rw [h1, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split_ifs <;> rfl
end Coding
