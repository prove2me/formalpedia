-- Prove2me | solution 1 for ClauseBound.Part.Lower.ratio_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:28:31.706186+00:00
-- url     : https://prove2.me/submissions/a4e0f687-1bb7-43c6-bc61-72c833c57887

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_Rec
import Definitions.Def_ClauseBound_Part_Lower
import Theorems.Thm_ClauseBound_Part_Lower_sqrt_sub_ge

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
open ClauseBound.Part.Lower
namespace ClauseBound.Part.Lower
theorem _root_.solution {c s x : ℝ} (B : ℕ) (hc : 0 ≤ c) (hs : 0 < s) (hx : 0 ≤ x) (hxs : x < s ^ 2) :
    Real.exp (c * s) / (s ^ 2) ^ B * (Real.exp (-((c / (2 * s) - B / s ^ 2) * x)) * (1 - c / (2 * s ^ 3) * x ^ 2))
      ≤ Real.exp (c * Real.sqrt (s ^ 2 - x)) / (s ^ 2 - x) ^ B := by
  have hs2 : 0 < s ^ 2 := by positivity
  have hd : 0 < s ^ 2 - x := by linarith
  have h1 : 1 - c / (2 * s ^ 3) * x ^ 2 ≤ Real.exp (-(c / (2 * s ^ 3) * x ^ 2)) := Real.one_sub_le_exp_neg _
  have h2 : (s ^ 2 - x) * Real.exp (x / s ^ 2) ≤ s ^ 2 := by
    have h3 : 1 - x / s ^ 2 ≤ Real.exp (-(x / s ^ 2)) := Real.one_sub_le_exp_neg _
    have h4 : s ^ 2 - x = s ^ 2 * (1 - x / s ^ 2) := by field_simp
    rw [h4, mul_assoc]
    have h5 : (1 - x / s ^ 2) * Real.exp (x / s ^ 2) ≤ 1 := by
      calc _ ≤ Real.exp (-(x / s ^ 2)) * Real.exp (x / s ^ 2) := mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
    nlinarith
  have h6 : (s ^ 2 - x) ^ B * Real.exp (B * (x / s ^ 2)) ≤ (s ^ 2) ^ B := by
    rw [Real.exp_nat_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h2 B
  have h7 : c * s - c / (2 * s) * x - c / (2 * s ^ 3) * x ^ 2 ≤ c * Real.sqrt (s ^ 2 - x) := by
    have := mul_le_mul_of_nonneg_left (sqrt_sub_ge hs hx hxs.le) hc
    calc _ = c * (s - x / (2 * s) - x ^ 2 / (2 * s ^ 3)) := by ring
      _ ≤ _ := this
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
  calc Real.exp (c * s) * (Real.exp (-((c / (2 * s) - B / s ^ 2) * x)) * (1 - c / (2 * s ^ 3) * x ^ 2)) * (s ^ 2 - x) ^ B
      ≤ Real.exp (c * s) * (Real.exp (-((c / (2 * s) - B / s ^ 2) * x)) * Real.exp (-(c / (2 * s ^ 3) * x ^ 2))) * (s ^ 2 - x) ^ B := by
        gcongr
    _ = Real.exp (c * s - c / (2 * s) * x - c / (2 * s ^ 3) * x ^ 2) * ((s ^ 2 - x) ^ B * Real.exp (B * (x / s ^ 2))) := by
        rw [← Real.exp_add, ← Real.exp_add, mul_comm ((s ^ 2 - x) ^ B) (Real.exp _), ← mul_assoc, ← Real.exp_add]
        congr 2
        ring
    _ ≤ Real.exp (c * Real.sqrt (s ^ 2 - x)) * (s ^ 2) ^ B := by
        gcongr
end ClauseBound.Part.Lower
