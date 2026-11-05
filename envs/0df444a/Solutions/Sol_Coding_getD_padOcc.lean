-- Prove2me | solution 1 for Coding.getD_padOcc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:23:40.059665+00:00
-- url     : https://prove2.me/submissions/1218b67f-cf18-42a4-9923-5ecf3aaf3ee8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_OccLinks
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_Eight_ViaGrouping_SatPsi
import Mathlib.Tactic.Ring
import Definitions.Def_Coding_Occ
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Coding
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight.SecNetworks Eight.ViaGrouping
variable {g : ℕ} {Φ : Fml}
namespace Coding
theorem _root_.solution (a : Fin g) (z : List Bool) {i : ℕ} (hi : i < mu g Φ * 3) :
    (padOcc g Φ a z).getD i false = (decide (i % 3 < (Φ.getD (a.val * mu g Φ + i / 3) []).length) && bitAt g Φ a.val z (a.val * mu g Φ + i / 3, i % 3)) := by
  rw [padOcc, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl
end Coding
