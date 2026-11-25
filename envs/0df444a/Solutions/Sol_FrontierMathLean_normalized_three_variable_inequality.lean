-- Prove2me | solution 1 for FrontierMathLean.normalized_three_variable_inequality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:47:22.994268+00:00
-- url     : https://prove2.me/submissions/072d2976-3090-4511-854e-52dae624da4f

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Definitions.Def_FrontierMathLean_AbstractInequality
import Theorems.Thm_FrontierMathLean_add_inv_mono_on_one

set_option autoImplicit false
open FrontierMathLean
namespace FrontierMathLean
theorem _root_.solution
    {x y r : ℝ} (hr : 1 ≤ r) (hrx : r ≤ x) (hry : r ≤ y) :
    5 + 2 * (r + r⁻¹) ≤
      3 + (x + x⁻¹) + (y + y⁻¹) + (x / y + y / x) := by
  have hx_pos : 0 < x := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hr) hrx
  have hy_pos : 0 < y := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hr) hry
  have hx := add_inv_mono_on_one hr hrx
  have hy := add_inv_mono_on_one hr hry
  have hxy : 2 ≤ x / y + y / x := by
    have hsquare : 0 ≤ (x - y) ^ 2 := sq_nonneg (x - y)
    field_simp [hx_pos.ne', hy_pos.ne']
    nlinarith
  linarith
end FrontierMathLean
