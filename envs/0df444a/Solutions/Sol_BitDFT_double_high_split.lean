-- Prove2me | solution 1 for BitDFT.double_high_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T01:45:56.942148+00:00
-- url     : https://prove2.me/submissions/936fc2ae-ae8f-4359-9ab8-15e670f5e168

import Theorems.Thm_BitDFT_scalar_low_product_selection
import Mathlib.Tactic

set_option autoImplicit false
open IntMul

/-- A product of two magnitudes at most `2^q` reduces to their low-word product;
    either high bit contributes only a shift. Thus one q-bit multiplier call
    suffices even when both magnitudes are on the boundary. -/
theorem solution (q a b : ℕ) (ha : a ≤ 2^q) (hb : b ≤ 2^q) :
    a * b = if a.testBit q then 2^q * b
      else if b.testBit q then (a % 2^q) * 2^q
      else (a % 2^q) * (b % 2^q) := by
  have hsa := (BitDFT.scalar_low_product_selection q a 1 ha).2.1
  have hsb := (BitDFT.scalar_low_product_selection q b (a % 2^q) hb).2.1
  by_cases hA : a.testBit q
  · rw [if_pos hA]
    have hsa' : a = 2^q := by
      rcases lt_or_eq_of_le ha with h | h
      · rw [Nat.testBit_eq_false_of_lt h] at hA
        contradiction
      · exact h
    rw [hsa']
  · rw [if_neg hA]
    have hsa' : a = a % 2^q := by simpa [hA] using hsa
    rw [hsa', hsb]
    have hlowA : a % 2^q < 2^q := Nat.mod_lt _ (by positivity)
    have hmodA : (a % 2^q) % 2^q = a % 2^q := Nat.mod_eq_of_lt hlowA
    simp [hmodA]
