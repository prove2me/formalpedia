-- Prove2me | solution 1 for Exits.stCountNil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:43:45.479887+00:00
-- url     : https://prove2.me/submissions/11c37d1c-db37-43b2-b71b-290815a5fcc4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_AlgDefs
import Definitions.Def_Exits_Level
import Definitions.Def_Eight_ViaGrouping_Count
import Definitions.Def_ToTuring_Poly_Comb
import Mathlib.Tactic.Positivity
import Definitions.Def_Exits_Count
import Theorems.Thm_Groundwork_Stepped_const_runs
import Theorems.Thm_Groundwork_Stepped_ite_runs_true


set_option autoImplicit false
section
section
open Exits
open Groundwork Groundwork.Prog Groundwork.Stepped Paper Eight Eight.SecNetworks Eight.ViaGrouping
namespace Exits
theorem _root_.solution : StCountNil := fun _ => ⟨_, ite_runs_true rfl (const_runs (1 : ℤ) ([] : Formula))⟩
end Exits
