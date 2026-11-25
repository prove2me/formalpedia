-- Prove2me | solution 1 for FrontierMathLean.add_inv_mono_on_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:36:32.31998+00:00
-- url     : https://prove2.me/submissions/220585f2-378a-4954-947f-3c6d8c8e7c76

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Definitions.Def_FrontierMathLean_AbstractInequality

set_option autoImplicit false
open FrontierMathLean
namespace FrontierMathLean
theorem _root_.solution
    {x r : ℝ} (hr : 1 ≤ r) (hrx : r ≤ x) :
    r + r⁻¹ ≤ x + x⁻¹ := by
  have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hx_pos : 0 < x := lt_of_lt_of_le hr_pos hrx
  have h₁ : 0 ≤ x - r := sub_nonneg.mpr hrx
  have h₂ : 0 ≤ 1 - (x * r)⁻¹ := by
    rw [sub_nonneg]
    apply (inv_le_one₀ (mul_pos hx_pos hr_pos)).2
    have hx_one : 1 ≤ x := le_trans hr hrx
    nlinarith [mul_nonneg (sub_nonneg.mpr hx_one) (sub_nonneg.mpr hr)]
  have hprod : 0 ≤ (x - r) * (1 - (x * r)⁻¹) := mul_nonneg h₁ h₂
  field_simp [hx_pos.ne', hr_pos.ne'] at hprod ⊢
  nlinarith
end FrontierMathLean
