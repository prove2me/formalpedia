-- Prove2me | solution 1 for ExplicitCost.size_map_fst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:48:52.961876+00:00
-- url     : https://prove2.me/submissions/6ccf74b0-71be-49a6-8f56-b6604c4cc54e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_EntryDefs
import Definitions.Def_ExplicitCost_Mirror
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_SameRuns
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
variable (K g : ℕ)
namespace ExplicitCost
theorem _root_.solution {α α' β : Type} [HasSize α] [HasSize α'] [HasSize β] {w : α → α'} {d : ℕ} (hw : ∀ a, size (w a) ≤ size a + d) (p : α × β) : size (Prod.map w id p) ≤ size p + d := by
  change size (w p.1) + size p.2 ≤ size p.1 + size p.2 + d
  have := hw p.1
  omega
end ExplicitCost
