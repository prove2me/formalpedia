-- Prove2me | solution 1 for Eight.ViaGrouping.exponent_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:29:44.357581+00:00
-- url     : https://prove2.me/submissions/de311273-3e7c-49ff-b46f-9099d9919876

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Search
import Definitions.Def_StepMachines_Math_RebalanceArith
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Main

set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Cost
namespace Eight.ViaGrouping
theorem _root_.solution (e U g P K : ℝ) : e * U + (e + 2) * (g * P) / K = e * (U + g * P / K) + 2 * (g * P) / K := by ring
end Eight.ViaGrouping
