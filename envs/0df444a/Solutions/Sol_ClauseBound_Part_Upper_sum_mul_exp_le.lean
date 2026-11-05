-- Prove2me | solution 1 for ClauseBound.Part.Upper.sum_mul_exp_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:28:30.317095+00:00
-- url     : https://prove2.me/submissions/7f0accc6-2642-46b3-b766-3dc5e9a0ec18

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_Rec
import Definitions.Def_ClauseBound_Part_Upper
import Theorems.Thm_ClauseBound_Part_Upper_exp_div_le

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
open ClauseBound.Part.Upper
namespace ClauseBound.Part.Upper
theorem _root_.solution {y : ℝ} (hy : 0 < y) (s : Finset ℕ) : ∑ v ∈ s, (v : ℝ) * Real.exp (-(y * v)) ≤ 1 / y ^ 2 := by
  have hr0 : 0 < Real.exp (-y) := Real.exp_pos _
  have hlt : Real.exp (-y) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hsum := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := Real.exp (-y)) (by rwa [Real.norm_eq_abs, abs_of_pos hr0])
  have h1 : ∑ v ∈ s, (v : ℝ) * Real.exp (-(y * v)) = ∑ v ∈ s, (v : ℝ) * Real.exp (-y) ^ v := by
    refine sum_congr rfl fun v _ => ?_
    rw [← Real.exp_nat_mul]
    congr 2
    ring
  rw [h1]
  exact (sum_le_hasSum s (fun _ _ => by positivity) hsum).trans (exp_div_le hy)
end ClauseBound.Part.Upper
