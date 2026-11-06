-- Prove2me | solution 1 for Coding.zero_padOcc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:44:09.249226+00:00
-- url     : https://prove2.me/submissions/dc6f243a-6085-4960-ade2-72066fcf45a8

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
import Theorems.Thm_Coding_litAt_local
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Count_locals_eq
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Coding
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight.SecNetworks Eight.ViaGrouping
variable {g : ℕ} {Φ : Fml}
namespace Coding
theorem _root_.solution (hg : 0 < g) (a : Fin g) (z : List Bool) :
    ((locals g 3 Φ).all fun r => (litAt 3 Φ (a.val * (mu g Φ * 3) + r)).isSome || !((padOcc g Φ a z).getD r false)) = true := by
  rw [locals_eq hg, List.all_eq_true]
  intro r hr
  rw [getD_padOcc a z (List.mem_range.1 hr), litAt_local]
  by_cases h : r % 3 < (Φ.getD (a.val * mu g Φ + r / 3) []).length
  · rw [if_pos h]; rfl
  · rw [if_neg h, decide_eq_false h]; rfl
end Coding
