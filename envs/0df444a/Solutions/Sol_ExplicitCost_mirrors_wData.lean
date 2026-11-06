-- Prove2me | solution 1 for ExplicitCost.mirrors_wData
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:51:28.997199+00:00
-- url     : https://prove2.me/submissions/dc9c4c30-abdb-4f31-bd3b-5fd3fc875496

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_EntryDefs
import Definitions.Def_ExplicitCost_Mirror
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_SameRuns
import Theorems.Thm_ExplicitCost_mirrors_mem
import Theorems.Thm_ExplicitCost_mirrors_W
import Theorems.Thm_P2M_ExplicitCost_size_widen__afc97683d577
import Theorems.Thm_ExplicitCost_qW_widen
import Theorems.Thm_ExplicitCost_Mirrors_gated
import Theorems.Thm_ExplicitCost_Mirrors_mapIn


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
variable (K g : ℕ)
namespace ExplicitCost
theorem _root_.solution : Mirrors (wQ K g asked) wData (widen₂ K g) (2 * (2 * K + 2 * g + 2)) :=
  Mirrors.gated ((mirrors_mem K g).mapIn (qW_widen K g)) ((mirrors_W K g).mapIn (qW_widen K g)) (size_widen₂ K g) (by omega) (by omega)
end ExplicitCost
