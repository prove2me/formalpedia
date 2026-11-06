-- Prove2me | solution 1 for Exits.stGroupingLemmaOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:04:28.707121+00:00
-- url     : https://prove2.me/submissions/dd5fc39d-dd27-4018-832e-226023076819

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_AlgDefs
import Definitions.Def_Eight_ViaGrouping_Main
import Definitions.Def_Eight_ViaGrouping_Keeps
import Definitions.Def_ToTuring_Poly_Range
import Mathlib.Tactic.GCongr
import Definitions.Def_Exits_Grouping
import Theorems.Thm_Exits_correct_of_searchStops

set_option autoImplicit false
section
section
open Exits
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Stepped Finset Paper Eight Eight.SecNetworks Eight.ViaGrouping Eight.ViaGrouping.Cost
namespace Exits
theorem _root_.solution : StGroupingLemmaOf := fun hR hS hT hV K _ _ hK h0 h =>
  correct_of_searchStops hR hT hV hK (by
    have : K ≤ K ^ 8 := Nat.le_self_pow (by norm_num) K
    omega) h0 h fun C _ Np c N P B τ S hN => hS K hK C Np c N P B τ S hN
end Exits
