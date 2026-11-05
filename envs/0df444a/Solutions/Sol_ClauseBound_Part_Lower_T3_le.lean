-- Prove2me | solution 1 for ClauseBound.Part.Lower.T3_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:32:33.977676+00:00
-- url     : https://prove2.me/submissions/7c0834a5-a4b7-4062-89a7-c6f8153c1e4f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_Rec
import Definitions.Def_ClauseBound_Part_Lower
import Theorems.Thm_ClauseBound_Part_Lower_cube_le

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
open ClauseBound.Part.Lower
namespace ClauseBound.Part.Lower
theorem _root_.solution {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) : ∑' v : ℕ, (v : ℝ) ^ 3 * r ^ v ≤ 6 / (1 - r) ^ 4 := by
  have hr : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg h0]
  have hs := (summable_pow_mul_geometric_of_norm_lt_one 3 hr).hasSum
  have hc := (hasSum_choose_mul_geometric_of_norm_lt_one 3 hr).mul_left 6
  refine (hasSum_le (fun v => ?_) hs hc).trans (le_of_eq (by ring))
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (cube_le v) (by positivity)
end ClauseBound.Part.Lower
