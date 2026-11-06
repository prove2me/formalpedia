-- Prove2me | solution 1 for ExplicitCost.mirrors_fData
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:42:11.899722+00:00
-- url     : https://prove2.me/submissions/6d5130bc-b16e-4021-996e-1dd5c7224945

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_EntryDefs
import Definitions.Def_ExplicitCost_Mirror
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_SameRuns
import Theorems.Thm_ExplicitCost_mirrors_mem
import Theorems.Thm_ExplicitCost_mirrors_f
import Theorems.Thm_P2M_ExplicitCost_size_widen__afc97683d577
import Theorems.Thm_ExplicitCost_qW_widen
import Theorems.Thm_ExplicitCost_qF_widen
import Theorems.Thm_ExplicitCost_Mirrors_gated
import Theorems.Thm_ExplicitCost_Mirrors_mapIn


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
variable (K g : ℕ)
namespace ExplicitCost
theorem _root_.solution : Mirrors (fQ K g asked) fData (widen₂ K g) (2 * (2 * K + 2 * g + 2)) :=
  Mirrors.gated ((mirrors_mem K g).mapIn (qW_widen K g)) ((mirrors_f K g).mapIn (qF_widen K g)) (size_widen₂ K g) (by omega) (by omega)
end ExplicitCost
