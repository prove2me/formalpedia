-- Prove2me | solution 1 for BitDFT.scaled_call_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T22:07:46.035655+00:00
-- url     : https://prove2.me/submissions/bcd7ad1d-b743-42ec-9fc3-ac77fa4785d6

import Theorems.Thm_BitDFT_clean_multiplier_call
import Theorems.Thm_BitDFT_scalar_low_product_selection
import Theorems.Thm_BitDFT_scaled_product_word_direct
import Theorems.Thm_BitDFT_bin_padding
import Definitions.Def_BitDFT_Encoding
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

set_option autoImplicit false
open BitDFT IntMul

private theorem bin_succ (k z : ℕ) : bin (k+1) z = bin k (z/2) ++ [z.testBit 0] := by
  unfold bin
  rw [List.ofFn_succ',List.concat_eq_append]
  congr 1
  · congr 1
    funext i
    rw [Nat.testBit_div_two]
    congr 1
    simp only [Fin.val_castSucc]
    omega
  · simp

private theorem val_append_bit (w : List Bool) (b : Bool) :
    val (w++[b]) = 2*val w+b.toNat := by
  simp [val,List.foldl_append]

private theorem low_bit (z : ℕ) : (z.testBit 0).toNat = z%2 := by
  have h := Nat.mod_lt z (by decide : 0 < 2)
  simp only [Nat.testBit_eq_decide_div_mod_eq,Nat.pow_zero,Nat.div_one]
  by_cases hz : z%2 = 1
  · simp [hz]
  · have h0 : z%2 = 0 := by omega
    simp [h0]

private theorem val_bin (k z : ℕ) (hz : z < 2^k) : val (bin k z) = z := by
  induction k generalizing z with
  | zero =>
    have h : z=0 := by simpa using hz
    subst z
    rfl
  | succ k ih =>
    rw [bin_succ,val_append_bit,ih,low_bit]
    · omega
    · have hpow : 2^(k+1) = 2^k*2 := pow_succ _ _
      omega

/-- A real q-bit multiplier call and its widened serialization target are
    linked in one theorem. The largest legal magnitude uses the same call on
    its low q bits, then selects the exact shifted result for serialization. -/
theorem solution (M : MultitapeTM) (q n a : ℕ) (T : ℝ)
    (hq : 1 ≤ q) (hnq : n < 2^q) (hqwide : lg n + 1 ≤ q)
    (hnwide : n ≤ 2^(lg n)) (ha : a ≤ 2^q)
    (hM : MultipliesAt M q T) :
    ∃ t : ℕ, (t : ℝ) ≤ 36*T ∧
      (IntMul.TrackedNativeCall.machine M).HaltsWithOutput
        (bin q n) (bin q (a%2^q)) t (bin (2*q) (n*(a%2^q))) ∧
      (if a.testBit q then n*2^q else n*(a%2^q)) = n*a ∧
      bin (2*q) (if a.testBit q then n*2^q else n*(a%2^q)) =
        List.replicate (2*q-(q+lg n+1)) false ++
          bin (q+lg n+1) (if a.testBit q then n*2^q else n*(a%2^q)) := by
  have hlow : a%2^q < 2^q := Nat.mod_lt _ (by positivity)
  have hnval := val_bin q n hnq
  have haval := val_bin q (a%2^q) hlow
  have hx : (bin q n).length = q := by simp [bin]
  have hy : (bin q (a%2^q)).length = q := by simp [bin]
  obtain ⟨t,ht,ho⟩ := BitDFT.clean_multiplier_call M q T hq hM
    (bin q n) (bin q (a%2^q)) hx hy
  have hsel := BitDFT.scalar_low_product_selection q a n ha
  have hword : bin (2*q) (if a.testBit q then n*2^q else n*(a%2^q)) =
      List.replicate (2*q-(q+lg n+1)) false ++
        bin (q+lg n+1) (if a.testBit q then n*2^q else n*(a%2^q)) := by
    by_cases hb : a.testBit q
    · have he : a = 2^q := by
        rcases lt_or_eq_of_le ha with h | h
        · rw [Nat.testBit_eq_false_of_lt h] at hb
          contradiction
        · exact h
      have hf : n*2^q < 2^(q+lg n+1) := by
        calc
          n*2^q ≤ 2^(lg n)*2^q := Nat.mul_le_mul_right _ hnwide
          _ = 2^(q+lg n) := by rw [pow_add,Nat.mul_comm]
          _ < 2^(q+lg n+1) := by
            rw [pow_succ]
            have hp : 0 < 2^(q+lg n) := by positivity
            nlinarith
      have hw : q+lg n+1 ≤ 2*q := by omega
      have hs : (q+lg n+1)+(2*q-(q+lg n+1))=2*q := by omega
      have hp := BitDFT.bin_padding (q+lg n+1) (2*q-(q+lg n+1)) (n*2^q) hf
      simpa [he,hb,hs] using hp
    · have hp := BitDFT.scaled_product_word_direct q n a hqwide hnwide ha
      simpa [hb] using hp.2
  refine ⟨t,ht,?_,hsel.2.1.symm,hword⟩
  · simpa only [hnval,haval] using ho.1
