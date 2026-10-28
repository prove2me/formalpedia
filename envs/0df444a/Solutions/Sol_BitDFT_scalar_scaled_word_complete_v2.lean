-- Prove2me | solution 1 for BitDFT.scalar_scaled_word_complete_v2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T22:04:19.963961+00:00
-- url     : https://prove2.me/submissions/92671795-ed06-4e8c-8289-ce9920677a73

import Theorems.Thm_BitDFT_bin_padding
import Theorems.Thm_BitDFT_scalar_low_product_selection
import Theorems.Thm_BitDFT_scaled_product_word_direct
import Mathlib.Tactic

set_option autoImplicit false
open IntMul

/-- A q-bit multiplier call followed by the high-bit selection serializes the
    exact product at the scaler's wider output width, including the boundary
    magnitude `2^q`. -/
theorem solution (q n a : ℕ) (hq : lg n + 1 ≤ q)
    (hn : n ≤ 2^(lg n)) (ha : a ≤ 2^q) :
    (if a.testBit q then n * 2^q else n * (a % 2^q)) = n * a ∧
    (if a.testBit q then n * 2^q else n * (a % 2^q)) < 2^(q + lg n + 1) ∧
    bin (2*q) (if a.testBit q then n * 2^q else n * (a % 2^q)) =
      List.replicate (2*q-(q+lg n+1)) false ++
      bin (q+lg n+1) (if a.testBit q then n * 2^q else n * (a % 2^q)) := by
  have hsel := BitDFT.scalar_low_product_selection q a n ha
  rcases hsel with ⟨_, hprod, _⟩
  have hbound : n ≤ 2^(lg n) := hn
  have hfull : n * 2^q < 2^(q+lg n+1) := by
    calc
      n * 2^q ≤ 2^(lg n) * 2^q := Nat.mul_le_mul_right _ hbound
      _ = 2^(q+lg n) := by rw [pow_add, Nat.mul_comm]
      _ < 2^(q+lg n+1) := by
        rw [pow_succ]
        have hp : 0 < 2^(q+lg n) := by positivity
        nlinarith
  have hlow := BitDFT.scaled_product_word_direct q n a hq hn ha
  rcases hlow with ⟨hlow_bound, hlow_word⟩
  constructor
  · exact hprod.symm
  constructor
  · by_cases hb : a.testBit q
    · simpa [hb] using hfull
    · simpa [hb] using hlow_bound
  · by_cases hb : a.testBit q
    · have he : a = 2^q := by
        rcases lt_or_eq_of_le ha with h | h
        · rw [Nat.testBit_eq_false_of_lt h] at hb
          contradiction
        · exact h
      have hword : bin (2*q) (n * 2^q) =
          List.replicate (2*q-(q+lg n+1)) false ++ bin (q+lg n+1) (n*2^q) := by
        have hwidth : q+lg n+1 ≤ 2*q := by omega
        have hsum : (q+lg n+1)+(2*q-(q+lg n+1))=2*q := by omega
        simpa [hsum] using
          BitDFT.bin_padding (q+lg n+1) (2*q-(q+lg n+1)) (n*2^q) hfull
      simpa [he, hb] using hword
    · simpa [hb] using hlow_word
