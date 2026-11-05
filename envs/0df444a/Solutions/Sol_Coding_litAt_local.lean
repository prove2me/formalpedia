-- Prove2me | solution 1 for Coding.litAt_local
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T03:07:42.641024+00:00
-- url     : https://prove2.me/submissions/620409e1-b956-44d3-b6f7-4edca130f772

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_OccLinks
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_Eight_ViaGrouping_SatPsi
import Mathlib.Tactic.Ring
import Definitions.Def_Coding_Occ
import Theorems.Thm_Coding_litAt_eq
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
theorem _root_.solution (a r : ℕ) : litAt 3 Φ (a * (mu g Φ * 3) + r) = if r % 3 < (Φ.getD (a * mu g Φ + r / 3) []).length then some (litOf Φ (a * mu g Φ + r / 3, r % 3)) else none := by
  have e : a * (mu g Φ * 3) = a * mu g Φ * 3 := by ring
  have e1 : (a * mu g Φ * 3 + r) / 3 = a * mu g Φ + r / 3 := by omega
  have e2 : (a * mu g Φ * 3 + r) % 3 = r % 3 := by omega
  rw [litAt_eq, e, e1, e2]
end Coding
