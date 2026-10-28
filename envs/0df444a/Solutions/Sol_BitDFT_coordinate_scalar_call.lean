-- Prove2me | solution 1 for BitDFT.coordinate_scalar_call
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T08:46:47.068852+00:00
-- url     : https://prove2.me/submissions/a27e7937-a16b-44c2-9db5-9de60e81f367

import Theorems.Thm_BitDFT_clean_multiplier_call
import Theorems.Thm_BitDFT_scalar_low_product_selection
import Theorems.Thm_BitDFT_scalar_product_width
import Definitions.Def_BitDFT_Encoding
import Mathlib.Tactic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.OfFn

set_option autoImplicit false
open IntMul

private theorem bin_succ (k z : ℕ) : bin (k+1) z = bin k (z/2) ++ [z.testBit 0] := by
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

private theorem val_append_bit (w : List Bool) (b : Bool) :
    val (w ++ [b]) = 2*val w + b.toNat := by
  simp [val, List.foldl_append]

private theorem low_bit (z : ℕ) : (z.testBit 0).toNat = z%2 := by
  have h := Nat.mod_lt z (by decide : 0 < 2)
  simp only [Nat.testBit_eq_decide_div_mod_eq, Nat.pow_zero, Nat.div_one]
  by_cases hz : z%2 = 1
  · simp [hz]
  · have h0 : z%2 = 0 := by omega
    simp [h0]

private theorem val_bin (k z : ℕ) (hz : z < 2^k) : val (bin k z) = z := by
  induction k generalizing z with
  | zero =>
      have h : z = 0 := by simpa using hz
      subst z
      rfl
  | succ k ih =>
      rw [bin_succ, val_append_bit, ih, low_bit]
      · omega
      · have hpow : 2^(k+1) = 2^k*2 := pow_succ _ _
        omega

/-- A signed coordinate bounded by `2^q` is multiplied using only the
    supplied q-bit multiplier. The theorem includes the boundary case and the
    exact output-width/sign guarantees needed by the rescaling controller. -/
theorem solution (M : MultitapeTM) (q n : ℕ) (T : ℝ) (z : ℤ)
    (hq : 1 ≤ q) (hn : n < 2^q) (hz : z.natAbs ≤ 2^q)
    (hM : MultipliesAt M q T) :
    ∃ t : ℕ,
      (t : ℝ) ≤ 36*T ∧
      (IntMul.TrackedNativeCall.machine M).HaltsWithOutput
        (bin q n) (bin q (z.natAbs % 2^q)) t
        (bin (2*q) (n*(z.natAbs % 2^q))) ∧
      n*z.natAbs = (if z.natAbs.testBit q then n*2^q
        else n*(z.natAbs % 2^q)) ∧
      ((n : ℤ)*z).natAbs < 2^(q+lg n+1) ∧
      (0 < n → (((n : ℤ)*z < 0) ↔ z < 0)) := by
  have hlow : z.natAbs % 2^q < 2^q := Nat.mod_lt _ (by positivity)
  have hnval := val_bin q n hn
  have haval := val_bin q (z.natAbs % 2^q) hlow
  have hx : (bin q n).length = q := by simp [bin]
  have hy : (bin q (z.natAbs % 2^q)).length = q := by simp [bin]
  obtain ⟨t, ht, ho⟩ := BitDFT.clean_multiplier_call M q T hq hM
    (bin q n) (bin q (z.natAbs % 2^q)) hx hy
  have hsel := BitDFT.scalar_low_product_selection q z.natAbs n hz
  have hwidth := BitDFT.scalar_product_width n q z hz
  refine ⟨t, ht, ?_, hsel.2.1, hwidth.1, hwidth.2⟩
  simpa only [hnval, haval] using ho.1
