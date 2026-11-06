-- Prove2me | solution 1 for ExplicitCost.entrySameRuns
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:00:57.269483+00:00
-- url     : https://prove2.me/submissions/fb7ff9b3-98e8-4d21-9b02-7c7d2ce215cd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_EntryDefs
import Definitions.Def_ExplicitCost_Mirror
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_SameRuns
import Theorems.Thm_ExplicitCost_mirrors_entryData
import Theorems.Thm_ExplicitCost_Mirrors_runs


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
variable (K g : ℕ)
namespace ExplicitCost
theorem _root_.solution : EntrySameRuns := fun K g _ _ _ _ _ _ _ _ h => (mirrors_entryData K g).runs h
end ExplicitCost
