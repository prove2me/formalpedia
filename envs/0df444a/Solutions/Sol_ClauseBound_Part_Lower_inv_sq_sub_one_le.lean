-- Prove2me | solution 1 for ClauseBound.Part.Lower.inv_sq_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:31:06.846164+00:00
-- url     : https://prove2.me/submissions/e19b9de8-f035-4782-a465-3b2c2bc31754

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_Rec
import Definitions.Def_ClauseBound_Part_Lower
import Theorems.Thm_ClauseBound_Part_Lower_sinh_le_mul_cosh

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
open ClauseBound.Part.Lower
namespace ClauseBound.Part.Lower
theorem _root_.solution {z : ℝ} (hz : 0 < z) : 1 / z ^ 2 - 1 ≤ 1 / Real.sinh z ^ 2 := by
  have hsh : 0 < Real.sinh z := Real.sinh_pos_iff.2 hz
  have hch : 0 < Real.cosh z := Real.cosh_pos z
  have key : (1 - z ^ 2) * Real.sinh z ^ 2 ≤ z ^ 2 := by
    rcases le_total (1 - z ^ 2) 0 with h | h
    · have : (1 - z ^ 2) * Real.sinh z ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (by positivity)
      nlinarith
    · have h1 : Real.sinh z ^ 2 ≤ (z * Real.cosh z) ^ 2 := pow_le_pow_left₀ hsh.le (sinh_le_mul_cosh hz.le) 2
      have h2 : Real.cosh z ^ 2 ≤ Real.exp (z ^ 2) := by
        calc Real.cosh z ^ 2 ≤ Real.exp (z ^ 2 / 2) ^ 2 := pow_le_pow_left₀ hch.le (Real.cosh_le_exp_half_sq z) 2
          _ = Real.exp (z ^ 2) := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      have h3 : (1 - z ^ 2) * Real.exp (z ^ 2) ≤ 1 := by
        calc _ ≤ Real.exp (-z ^ 2) * Real.exp (z ^ 2) := mul_le_mul_of_nonneg_right (Real.one_sub_le_exp_neg _) (Real.exp_pos _).le
          _ = 1 := by rw [← Real.exp_add]; simp
      calc (1 - z ^ 2) * Real.sinh z ^ 2 ≤ (1 - z ^ 2) * (z * Real.cosh z) ^ 2 := mul_le_mul_of_nonneg_left h1 h
        _ = z ^ 2 * ((1 - z ^ 2) * Real.cosh z ^ 2) := by ring
        _ ≤ z ^ 2 * ((1 - z ^ 2) * Real.exp (z ^ 2)) := by gcongr
        _ ≤ z ^ 2 * 1 := by gcongr
        _ = z ^ 2 := mul_one _
  rw [div_sub_one (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  linarith
end ClauseBound.Part.Lower
