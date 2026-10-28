-- Prove2me | solution 1 for BitDFT.double_high_multiplier_call
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T01:49:31.621207+00:00
-- url     : https://prove2.me/submissions/b232463e-8a3b-4810-a721-185f2076f728

import Theorems.Thm_BitDFT_clean_multiplier_call
import Theorems.Thm_BitDFT_scalar_low_product_selection
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

set_option autoImplicit false
open IntMul

namespace BitDFT.DoubleHighCallLemmas

theorem bin_succ (k z : ℕ) : bin (k+1) z = bin k (z/2) ++ [z.testBit 0] := by
  unfold bin
  rw [List.ofFn_succ', List.concat_eq_append]
  congr 1
  · congr 1
    funext i
    rw [Nat.testBit_div_two]
    congr 1
    simp only [Fin.val_castSucc]
    omega
  · simp

theorem val_append_bit (w : List Bool) (b : Bool) :
    val (w ++ [b]) = 2 * val w + b.toNat := by
  simp [val, List.foldl_append]

theorem low_bit (z : ℕ) : (z.testBit 0).toNat = z % 2 := by
  have h := Nat.mod_lt z (by decide : 0 < 2)
  simp only [Nat.testBit_eq_decide_div_mod_eq, Nat.pow_zero, Nat.div_one]
  by_cases hz : z % 2 = 1
  · simp [hz]
  · have h0 : z % 2 = 0 := by omega
    simp [h0]

theorem val_bin (k z : ℕ) (hz : z < 2^k) : val (bin k z) = z := by
  induction k generalizing z with
  | zero =>
      have h : z = 0 := by simpa using hz
      subst z
      rfl
  | succ k ih =>
      rw [bin_succ, val_append_bit, ih, low_bit]
      · omega
      · have hpow : 2^(k+1) = 2^k * 2 := pow_succ _ _
        omega

end BitDFT.DoubleHighCallLemmas

/-- The clean call computes the unique nontrivial low-word product. The full
    product of two magnitudes up to `2^q` is recovered by high-bit shifts, so
    no `(q+1)`-bit multiplier bound is needed. -/
theorem solution (M : MultitapeTM) (q : ℕ) (a b : ℕ) (T : ℝ)
    (hq : 1 ≤ q) (ha : a ≤ 2^q) (hb : b ≤ 2^q)
    (hM : MultipliesAt M q T) :
    ∃ t : ℕ, (t : ℝ) ≤ 36 * T ∧
      (IntMul.TrackedNativeCall.machine M).HaltsWithOutput
        (bin q (a % 2^q)) (bin q (b % 2^q)) t
        (bin (2*q) ((a % 2^q) * (b % 2^q))) ∧
      a*b = if a.testBit q then 2^q*b
        else if b.testBit q then (a % 2^q)*2^q
        else (a % 2^q)*(b % 2^q) := by
  have hlowA : a % 2^q < 2^q := Nat.mod_lt _ (by positivity)
  have hlowB : b % 2^q < 2^q := Nat.mod_lt _ (by positivity)
  have hx : (bin q (a % 2^q)).length = q := by simp [bin]
  have hy : (bin q (b % 2^q)).length = q := by simp [bin]
  obtain ⟨t, ht, hout, _, _⟩ :=
    BitDFT.clean_multiplier_call M q T hq hM
      (bin q (a % 2^q)) (bin q (b % 2^q)) hx hy
  have hvalA := BitDFT.DoubleHighCallLemmas.val_bin q (a % 2^q) hlowA
  have hvalB := BitDFT.DoubleHighCallLemmas.val_bin q (b % 2^q) hlowB
  refine ⟨t, ht, ?_, ?_⟩
  · simpa only [hvalA, hvalB] using hout
  · have hsa := (BitDFT.scalar_low_product_selection q a 1 ha).2.1
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
      have hmodA : (a % 2^q) % 2^q = a % 2^q := Nat.mod_eq_of_lt hlowA
      simp [hmodA]
