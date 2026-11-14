-- Prove2me | solution 1 for ConsistentSubmodular.Chains.twoEdgeRatio_critical
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:31:34.119994+00:00
-- url     : https://prove2.me/submissions/e7b6011d-72e2-4862-9e0e-56f64ce18308

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_ConsecutiveChains

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Chains

theorem solution {x y : ℝ} (hy : 1 < y) (hyx : y < x)
    (hfx : (y / x ^ 2 * (x + y - 1) - (2 - y / x - 1 / y)) / (x + y - 1) ^ 2 = 0)
    (hfy : ((1 / y ^ 2 - 1 / x) * (x + y - 1) - (2 - y / x - 1 / y)) / (x + y - 1) ^ 2 = 0) :
    phi (y / x) = 0 ∧ twoEdgeRatio x y = y / x ^ 2 ∧
      twoEdgeRatio x y = (y / x) ^ 3 * (1 + y / x) := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hD : 0 < x + y - 1 := by linarith
  have hD2 : (x + y - 1) ^ 2 ≠ 0 := by positivity
  have hNx : 2 - y / x - 1 / y = y / x ^ 2 * (x + y - 1) := by
    have := (div_eq_zero_iff.mp hfx).resolve_right hD2
    linarith
  have hNy : 2 - y / x - 1 / y = (1 / y ^ 2 - 1 / x) * (x + y - 1) := by
    have := (div_eq_zero_iff.mp hfy).resolve_right hD2
    linarith
  -- Equating the two expressions for `R` gives `E₁ = 0`; `R = y/x²` gives `E₂ = 0`.
  have hE₁ : x ^ 2 - x * y ^ 2 - y ^ 3 = 0 := by
    have h' : y / x ^ 2 = 1 / y ^ 2 - 1 / x := mul_right_cancel₀ hD.ne' (hNx.symm.trans hNy)
    have hid : y / x ^ 2 - (1 / y ^ 2 - 1 / x) = -(x ^ 2 - x * y ^ 2 - y ^ 3) / (x ^ 2 * y ^ 2) := by
      field_simp
      ring
    have h0 : -(x ^ 2 - x * y ^ 2 - y ^ 3) / (x ^ 2 * y ^ 2) = 0 := by
      rw [← hid, h', sub_self]
    have := (div_eq_zero_iff.mp h0).resolve_right (by positivity)
    linarith
  have hE₂ : 2 * x ^ 2 * y - 2 * x * y ^ 2 - x ^ 2 - y ^ 3 + y ^ 2 = 0 := by
    have hid : 2 - y / x - 1 / y - y / x ^ 2 * (x + y - 1) =
        (2 * x ^ 2 * y - 2 * x * y ^ 2 - x ^ 2 - y ^ 3 + y ^ 2) / (x ^ 2 * y) := by
      field_simp
      ring
    have h0 : (2 * x ^ 2 * y - 2 * x * y ^ 2 - x ^ 2 - y ^ 3 + y ^ 2) / (x ^ 2 * y) = 0 := by
      rw [← hid, hNx, sub_self]
    exact (div_eq_zero_iff.mp h0).resolve_right (by positivity)
  have hG : y * (y ^ 4 + x * y ^ 3 - 2 * x ^ 2 * y ^ 2 - 3 * x ^ 3 * y + 2 * x ^ 4) = 0 := by
    linear_combination (x ^ 2 - y ^ 2) * hE₁ + x ^ 2 * hE₂
  have hG' : y ^ 4 + x * y ^ 3 - 2 * x ^ 2 * y ^ 2 - 3 * x ^ 3 * y + 2 * x ^ 4 = 0 :=
    (mul_eq_zero.mp hG).resolve_left hy0.ne'
  have hR : twoEdgeRatio x y = y / x ^ 2 := by
    unfold twoEdgeRatio
    rw [hNx, mul_div_assoc, div_self hD.ne', mul_one]
  refine ⟨?_, hR, ?_⟩
  · have hid : phi (y / x) =
        (y ^ 4 + x * y ^ 3 - 2 * x ^ 2 * y ^ 2 - 3 * x ^ 3 * y + 2 * x ^ 4) / x ^ 4 := by
      unfold phi
      field_simp
    rw [hid, hG', zero_div]
  · have hid : y / x ^ 2 - (y / x) ^ 3 * (1 + y / x) = y * (x ^ 2 - x * y ^ 2 - y ^ 3) / x ^ 4 := by
      field_simp
      ring
    rw [hR, ← sub_eq_zero, hid, hE₁, mul_zero, zero_div]

end
