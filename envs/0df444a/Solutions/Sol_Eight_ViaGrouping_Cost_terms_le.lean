-- Prove2me | solution 1 for Eight.ViaGrouping.Cost.terms_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:28:19.69217+00:00
-- url     : https://prove2.me/submissions/5cc72079-d643-4396-8fa1-5f9d7cec8add

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Search
import Definitions.Def_StepMachines_Math_RebalanceArith
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Main
import Theorems.Thm_Eight_ViaGrouping_Cost_floor_le

set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Eight.ViaGrouping.Cost
namespace Eight.ViaGrouping.Cost
theorem _root_.solution (K g P : ℕ) : ((2 ^ (P * (2 * g / K)) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 * ((g : ℝ) * P) / K) := by
  rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (floor_le K g P)
end Eight.ViaGrouping.Cost
