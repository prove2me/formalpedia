-- Prove2me | solution 1 for Eight.ViaGrouping.Cost.floor_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:07:30.01349+00:00
-- url     : https://prove2.me/submissions/566b2bd7-08ba-48ee-a8a8-f26db63d33d4

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
theorem _root_.solution (K g P : ℕ) : ((P * (2 * g / K) : ℕ) : ℝ) ≤ 2 * ((g : ℝ) * P) / K := by
  have h : ((2 * g / K : ℕ) : ℝ) ≤ ((2 * g : ℕ) : ℝ) / K := Nat.cast_div_le
  have hP : (0 : ℝ) ≤ P := Nat.cast_nonneg P
  calc ((P * (2 * g / K) : ℕ) : ℝ) = P * ((2 * g / K : ℕ) : ℝ) := by push_cast; ring
    _ ≤ P * (((2 * g : ℕ) : ℝ) / K) := mul_le_mul_of_nonneg_left h hP
    _ = 2 * ((g : ℝ) * P) / K := by push_cast; ring
end Eight.ViaGrouping.Cost
