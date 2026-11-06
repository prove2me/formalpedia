-- Prove2me | solution 1 for Eight.ViaGrouping.Cost.exponent_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:34:34.6242+00:00
-- url     : https://prove2.me/submissions/59bc6dd2-dbf6-4595-a97e-88e191d1b2cd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Search
import Definitions.Def_StepMachines_Math_RebalanceArith
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Main
import Theorems.Thm_Eight_ViaGrouping_Cost_K2L_le_real

set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Eight.ViaGrouping.Cost
namespace Eight.ViaGrouping.Cost
theorem _root_.solution {K : ℕ} (g U P : ℕ) {e : ℝ} (hK : 1 ≤ K) (h0 : 0 ≤ e) :
    e * (K : ℝ) ^ 2 * (Paper.groupedLength K g U P : ℝ) + 2 * ((g : ℝ) * P) / K ≤ e * (K : ℝ) ^ 2 + (e * U + (e + 2) * ((g : ℝ) * P) / K) := by
  have h := mul_le_mul_of_nonneg_left (K2L_le_real g U P hK) h0
  have e1 : (e + 2) * ((g : ℝ) * P) / K = e * ((g : ℝ) * P / K) + 2 * ((g : ℝ) * P) / K := by ring
  rw [e1]
  linarith
end Eight.ViaGrouping.Cost
