-- Prove2me | solution 1 for ClauseBound.Part.Lower.T1_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:32:31.210198+00:00
-- url     : https://prove2.me/submissions/f101601e-b65f-4b4c-b641-47fac81c079d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_Rec
import Definitions.Def_ClauseBound_Part_Lower
import Theorems.Thm_ClauseBound_Part_Lower_inv_sq_sub_one_le

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
open ClauseBound.Part.Lower
namespace ClauseBound.Part.Lower
theorem _root_.solution {y : ℝ} (hy : 0 < y) : 1 / y ^ 2 - 1 / 4 ≤ Real.exp (-y) / (1 - Real.exp (-y)) ^ 2 := by
  have h := inv_sq_sub_one_le (z := y / 2) (by positivity)
  have hE : 0 < Real.exp (y / 2) := Real.exp_pos _
  have hE1 : 1 < Real.exp (y / 2) := Real.one_lt_exp_iff.2 (by positivity)
  have e1 : Real.exp (-y) = 1 / Real.exp (y / 2) ^ 2 := by
    rw [← Real.exp_nat_mul, one_div, ← Real.exp_neg]; congr 1; push_cast; ring
  have e2 : Real.sinh (y / 2) = (Real.exp (y / 2) - 1 / Real.exp (y / 2)) / 2 := by
    rw [Real.sinh_eq, Real.exp_neg, one_div]
  rw [e2] at h
  rw [e1]
  generalize Real.exp (y / 2) = E at *
  have hE2 : 0 < E ^ 2 - 1 := by nlinarith
  have e3 : 1 / E ^ 2 / (1 - 1 / E ^ 2) ^ 2 = 1 / 4 * (1 / ((E - 1 / E) / 2) ^ 2) := by
    have : E - 1 / E = (E ^ 2 - 1) / E := by field_simp
    have h' : 1 - 1 / E ^ 2 = (E ^ 2 - 1) / E ^ 2 := by field_simp
    rw [this, h']
    field_simp
    norm_num
  rw [e3]
  have e4 : 1 / y ^ 2 - 1 / 4 = 1 / 4 * (1 / (y / 2) ^ 2 - 1) := by field_simp; norm_num
  rw [e4]
  gcongr
end ClauseBound.Part.Lower
