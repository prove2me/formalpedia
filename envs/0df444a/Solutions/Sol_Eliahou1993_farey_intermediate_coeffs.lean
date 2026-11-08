-- Prove2me | solution 1 for Eliahou1993.farey_intermediate_coeffs
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-07T14:39:06.026005+00:00
-- url     : https://prove2.me/submissions/89aa133a-8400-48d2-b7a3-bd0dcd0e715e

/-
Adapted from https://github.com/tangentproofs/eliahou-collatz-bounds
(commit 18cc351df2f942ddba4bf03feb9b75a70701497d, file Collatz/LinearForm.lean),
formalizing:
  Shalom Eliahou (1993), "The 3x + 1 problem: new lower bounds on nontrivial
  cycle lengths", Discrete Mathematics 118(1-3), pp. 45–56, Lemma 3.1.
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

MIT License

Copyright (c) 2026 Michal Wallace

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/
import Mathlib.Tactic
import Mathlib.Data.Rat.Cast.Order

theorem solution {p q p' q' x y : ℕ}
    (hq : 0 < q) (hq' : 0 < q') (hy : 0 < y)
    (hfarey : p' * q - p * q' = 1)
    (hleft : (p : ℚ) / q < x / y)
    (hright : (x : ℚ) / y < p' / q') :
    ∃ (a b : ℕ), 0 < a ∧ 0 < b ∧
      x = a * p + b * p' ∧ y = a * q + b * q' := by
  have hleftN : p * y < q * x := by
    have := (div_lt_div_iff₀ (Nat.cast_pos.mpr hq) (Nat.cast_pos.mpr hy)).mp hleft
    have : (p : ℚ) * y < q * x := by
      linarith [this]
    exact_mod_cast this
  have hrightN : q' * x < p' * y := by
    have := (div_lt_div_iff₀ (Nat.cast_pos.mpr hy) (Nat.cast_pos.mpr hq')).mp hright
    have : (q' : ℚ) * x < p' * y := by
      linarith [this]
    exact_mod_cast this
  refine ⟨p' * y - q' * x, q * x - p * y, Nat.sub_pos_of_lt hrightN,
    Nat.sub_pos_of_lt hleftN, ?_, ?_⟩
  · refine Int.natCast_inj.mp ?_
    have ha : ((p' * y - q' * x : ℕ) : ℤ) = (p' : ℤ) * y - (q' : ℤ) * x :=
      Int.natCast_sub (Nat.le_of_lt hrightN)
    have hb : ((q * x - p * y : ℕ) : ℤ) = (q : ℤ) * x - (p : ℤ) * y :=
      Int.natCast_sub (Nat.le_of_lt hleftN)
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, ha, hb]
    have hf : (p' : ℤ) * q - (p : ℤ) * q' = 1 := by
      have hle : p * q' ≤ p' * q := Nat.le_of_lt (Nat.lt_of_sub_eq_succ hfarey)
      calc
        (p' : ℤ) * q - (p : ℤ) * q' = ↑(p' * q - p * q') := by
          rw [← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_sub hle]
        _ = ↑(1 : ℕ) := by rw [hfarey]
        _ = 1 := by norm_num
    nlinarith [hf]
  · refine Int.natCast_inj.mp ?_
    have ha : ((p' * y - q' * x : ℕ) : ℤ) = (p' : ℤ) * y - (q' : ℤ) * x :=
      Int.natCast_sub (Nat.le_of_lt hrightN)
    have hb : ((q * x - p * y : ℕ) : ℤ) = (q : ℤ) * x - (p : ℤ) * y :=
      Int.natCast_sub (Nat.le_of_lt hleftN)
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, ha, hb]
    have hf : (p' : ℤ) * q - (p : ℤ) * q' = 1 := by
      have hle : p * q' ≤ p' * q := Nat.le_of_lt (Nat.lt_of_sub_eq_succ hfarey)
      calc
        (p' : ℤ) * q - (p : ℤ) * q' = ↑(p' * q - p * q') := by
          rw [← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_sub hle]
        _ = ↑(1 : ℕ) := by rw [hfarey]
        _ = 1 := by norm_num
    nlinarith [hf]
