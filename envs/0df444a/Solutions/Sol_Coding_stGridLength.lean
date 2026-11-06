-- Prove2me | solution 1 for Coding.stGridLength
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:38:17.749189+00:00
-- url     : https://prove2.me/submissions/99d81260-97dc-47b0-8b24-75a3f104b412

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
theorem _root_.solution : StGridLength := by
  intro g lam
  refine Nat.mul_le_mul_right _ ?_
  calc g * (g ^ 2 - 1) ≤ g * g ^ 2 := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ = g ^ 3 := by ring
end Coding
