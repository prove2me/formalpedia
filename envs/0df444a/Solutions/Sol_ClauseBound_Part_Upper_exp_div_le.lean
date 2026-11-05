-- Prove2me | solution 1 for ClauseBound.Part.Upper.exp_div_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:27:15.914572+00:00
-- url     : https://prove2.me/submissions/958bb395-08b1-45ea-9ca6-6f5ecbc62491

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_Rec
import Definitions.Def_ClauseBound_Part_Upper

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
open ClauseBound.Part.Upper
namespace ClauseBound.Part.Upper
theorem _root_.solution {y : ℝ} (hy : 0 < y) : Real.exp (-y) / (1 - Real.exp (-y)) ^ 2 ≤ 1 / y ^ 2 := by
  have hq : 0 < Real.exp (-(y / 2)) := Real.exp_pos _
  have hr : Real.exp (-y) = Real.exp (-(y / 2)) ^ 2 := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hone : Real.exp (y / 2) * Real.exp (-(y / 2)) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hsinh : y / 2 ≤ (Real.exp (y / 2) - Real.exp (-(y / 2))) / 2 := by
    rw [← Real.sinh_eq]
    exact Real.self_le_sinh_iff.2 (by positivity)
  have h1 : y * Real.exp (-(y / 2)) ≤ 1 - Real.exp (-(y / 2)) ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hsinh hq.le
    nlinarith
  have hlt : Real.exp (-y) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  rw [div_le_div_iff₀ (by have : 0 < 1 - Real.exp (-y) := by linarith
                          positivity) (by positivity), one_mul, hr]
  calc Real.exp (-(y / 2)) ^ 2 * y ^ 2 = (y * Real.exp (-(y / 2))) ^ 2 := by ring
    _ ≤ (1 - Real.exp (-(y / 2)) ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
end ClauseBound.Part.Upper
