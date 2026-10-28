-- Prove2me | solution 1 for CountingMatroid.Bridge.RationalPair.rationalPairOperations_preserve_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T21:38:51.659859+00:00
-- url     : https://prove2.me/submissions/984569e1-1895-4efd-84d4-f223c02eb7d7

import Definitions.Def_CountingMatroidBridgeNonnegativeRationalPair

set_option autoImplicit false
open CountingMatroid.Bridge.RationalPair

theorem solution (x y : Pair)
    (hx : 0 < x.2) (hy : 0 < y.2) (hyn : 0 < y.1) :
    value (add x y) = value x + value y ∧
    value (mul x y) = value x * value y ∧
    value (div x y) = value x / value y ∧
    (value x < value y ↔ x.1 * y.2 < y.1 * x.2) ∧
    0 ≤ value x ∧
    0 < (add x y).2 ∧ 0 < (mul x y).2 ∧ 0 < (div x y).2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [value, add]
    push_cast
    have hx0 : (x.2 : ℚ) ≠ 0 := by positivity
    have hy0 : (y.2 : ℚ) ≠ 0 := by positivity
    field_simp [hx0, hy0]
  · simp only [value, mul]
    push_cast
    have hx0 : (x.2 : ℚ) ≠ 0 := by positivity
    have hy0 : (y.2 : ℚ) ≠ 0 := by positivity
    field_simp [hx0, hy0]
  · simp only [value, div]
    push_cast
    have hx0 : (x.2 : ℚ) ≠ 0 := by positivity
    have hy0 : (y.2 : ℚ) ≠ 0 := by positivity
    have hyn0 : (y.1 : ℚ) ≠ 0 := by positivity
    field_simp [hx0, hy0, hyn0]
  · have hxq : (0 : ℚ) < (x.2 : ℚ) := by exact_mod_cast hx
    have hyq : (0 : ℚ) < (y.2 : ℚ) := by exact_mod_cast hy
    rw [value, value, div_lt_div_iff₀ hxq hyq]
    exact_mod_cast (show x.1 * y.2 < y.1 * x.2 ↔ x.1 * y.2 < y.1 * x.2 from Iff.rfl)
  · unfold value
    positivity
  · simp [add]
    exact ⟨hx, hy⟩
  · simp [mul]
    exact ⟨hx, hy⟩
  · simp [div]
    exact ⟨hx, hyn⟩
