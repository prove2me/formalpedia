-- Prove2me | solution 1 for Eight.ViaGrouping.stLemGrouping_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:58:52.537231+00:00
-- url     : https://prove2.me/submissions/3160a8be-b604-457b-9499-582b0a2bf8b1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Search
import Definitions.Def_StepMachines_Math_RebalanceArith
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Main
import Theorems.Thm_Eight_ViaGrouping_netAlg_correct

set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Cost
namespace Eight.ViaGrouping
theorem _root_.solution (hS : StSearch) (hT : StTable) (hV : StValue) : StLemGrouping := fun K _ _ hK h0 h =>
  netAlg_correct hT hV hK (by
    have : K ≤ K ^ 8 := Nat.le_self_pow (by norm_num) K
    omega) h0 h fun C _ Np c N P B τ S hN => hS K hK C Np c N P B τ S hN
end Eight.ViaGrouping
