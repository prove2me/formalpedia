-- Prove2me | solution 1 for ClauseBound.Part.Lower.sqrt_sub_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:27:26.84032+00:00
-- url     : https://prove2.me/submissions/8d7d1680-2435-419b-9e54-87699cd297e3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_Rec
import Definitions.Def_ClauseBound_Part_Lower

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
open ClauseBound.Part.Lower
namespace ClauseBound.Part.Lower
theorem _root_.solution {s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x) (hxs : x ≤ s ^ 2) :
    s - x / (2 * s) - x ^ 2 / (2 * s ^ 3) ≤ Real.sqrt (s ^ 2 - x) := by
  obtain ⟨y, rfl⟩ : ∃ y, x = y * s ^ 2 := ⟨x / s ^ 2, by field_simp⟩
  have hs2 : 0 < s ^ 2 := by positivity
  have hy0 : 0 ≤ y := by
    by_contra h
    have : y * s ^ 2 < 0 := mul_neg_of_neg_of_pos (not_le.1 h) hs2
    linarith
  have hy1 : y ≤ 1 := by
    by_contra h
    have : 1 * s ^ 2 < y * s ^ 2 := mul_lt_mul_of_pos_right (not_le.1 h) hs2
    linarith
  have e : s - y * s ^ 2 / (2 * s) - (y * s ^ 2) ^ 2 / (2 * s ^ 3) = s * (1 - y / 2 - y ^ 2 / 2) := by
    field_simp
  rw [e]
  refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
  have h1 : (1 - y / 2 - y ^ 2 / 2) ^ 2 ≤ 1 - y := by nlinarith [mul_nonneg hy0 hy0, mul_nonneg (mul_nonneg hy0 hy0) (sub_nonneg.2 hy1), mul_nonneg (mul_nonneg hy0 hy0) hy0]
  calc (s * (1 - y / 2 - y ^ 2 / 2)) ^ 2 = s ^ 2 * (1 - y / 2 - y ^ 2 / 2) ^ 2 := by ring
    _ ≤ s ^ 2 * (1 - y) := mul_le_mul_of_nonneg_left h1 hs2.le
    _ = s ^ 2 - y * s ^ 2 := by ring
end ClauseBound.Part.Lower
