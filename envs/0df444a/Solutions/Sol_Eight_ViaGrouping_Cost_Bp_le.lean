-- Prove2me | solution 1 for Eight.ViaGrouping.Cost.Bp_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:06:10.129225+00:00
-- url     : https://prove2.me/submissions/1dfe0cd8-a7b6-4f9e-a85a-f925e46415ab

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
open Eight.ViaGrouping.Cost
namespace Eight.ViaGrouping.Cost
theorem _root_.solution {K : ℕ} (g P B : ℕ) (hK : 1 ≤ K) : Bp K g P B ≤ (2 * g + g ^ 2) * (P + B) := by
  have h1 : ⌈2 * ((g : ℝ) * P) / K⌉₊ ≤ 2 * g * P := by
    refine Nat.ceil_le.2 ?_
    have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
    push_cast
    calc 2 * ((g : ℝ) * P) / K ≤ 2 * ((g : ℝ) * P) := div_le_self (by positivity) hK'
      _ = 2 * g * P := by ring
  have e : (2 * g + g ^ 2) * (P + B) = 2 * g * P + g ^ 2 * B + (2 * g * B + g ^ 2 * P) := by ring
  unfold Bp
  omega
end Eight.ViaGrouping.Cost
