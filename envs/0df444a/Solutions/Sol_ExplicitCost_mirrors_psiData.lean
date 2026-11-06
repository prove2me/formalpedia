-- Prove2me | solution 1 for ExplicitCost.mirrors_psiData
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:47:28.414743+00:00
-- url     : https://prove2.me/submissions/845f9cef-96d4-4a74-b03f-39e287bdf916

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_EntryDefs
import Definitions.Def_ExplicitCost_Mirror
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_SameRuns
import Theorems.Thm_ExplicitCost_mirrors_mem
import Theorems.Thm_P2M_ExplicitCost_mirrors___7c80e4a094aa
import Theorems.Thm_P2M_ExplicitCost_size_widen__afc97683d577
import Theorems.Thm_ExplicitCost_qW_widen
import Theorems.Thm_ExplicitCost_qMb_widen
import Theorems.Thm_ExplicitCost_qPsi_widen
import Theorems.Thm_ExplicitCost_Mirrors_gated
import Theorems.Thm_ExplicitCost_Mirrors_mapIn


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
variable (K g : ℕ)
namespace ExplicitCost
theorem _root_.solution : Mirrors (psiQ K g asked) psiData (widen₂ K g) (2 * (2 * K + 2 * g + 2)) :=
  Mirrors.gated ((mirrors_mem K g).mapIn (qW_widen K g))
    (Mirrors.gated (d := 2 * (2 * K + 2 * g + 2)) ((mirrors_mem K g).mapIn (qMb_widen K g)) ((mirrors_Ψ K g).mapIn (qPsi_widen K g)) (size_widen₂ K g) (by omega) (by omega))
    (size_widen₂ K g) (by omega) le_rfl
end ExplicitCost
