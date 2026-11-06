-- Prove2me | solution 1 for ExplicitCost.mirrors_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:27:57.920105+00:00
-- url     : https://prove2.me/submissions/95f95a5e-b913-4349-8c8d-597cbe03d68b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_EntryDefs
import Definitions.Def_ExplicitCost_Mirror
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_SameRuns
import Theorems.Thm_ExplicitCost_size_widenC
import Theorems.Thm_ExplicitCost_size_map_fst
import Theorems.Thm_ExplicitCost_Mirrors_mapOut
import Theorems.Thm_ExplicitCost_mirrors_query
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_Sparsify_StackOK_mem
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
variable (K g : ℕ)
namespace ExplicitCost
theorem _root_.solution : Mirrors asked.mem askedData.mem (Prod.map (widenC K g) id) (2 * K + 2 * g + 2) :=
  (mirrors_query (fun _ => rfl) (size_map_fst fun c => (size_widenC K g c).le)).mapOut _
end ExplicitCost
