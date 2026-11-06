-- Prove2me | solution 1 for Exits.stFoldUntil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:35:08.518329+00:00
-- url     : https://prove2.me/submissions/71466255-50af-430e-be05-427b2db0b3fe

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_Tested
import Definitions.Def_StepMachines_Prog_Range
import Definitions.Def_StepMachines_Prog_Range
import Definitions.Def_StepMachines_Prog_Walk
import Definitions.Def_StepMachines_Prog_Walk
import Definitions.Def_Exits_Runs
import Theorems.Thm_Exits_foldUntil_reaches

set_option autoImplicit false
section
section
open Exits
open Finset Groundwork Groundwork.Stepped
open Groundwork.Sparsify (leaves)
variable {α β γ τ ν : Type}
namespace Exits
theorem _root_.solution : StFoldUntil := by
  intro α β γ τ _ _ start nxt M g stop c₀ a xs ho t v Sx Sc Sm hM hx hc
  exact foldUntil_reaches ho t v Sx Sc Sm (c₀ a) hM hx hc
end Exits
