-- Prove2me | solution 1 for BitDFT.low_multiplier_call
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T19:13:59.442909+00:00
-- url     : https://prove2.me/submissions/356aa429-9e14-4f94-a76e-6ab984106b86

import Theorems.Thm_BitDFT_clean_multiplier_call
import Theorems.Thm_BitDFT_scalar_low_product_selection
import Mathlib.Tactic
import Definitions.Def_BitDFT_Encoding
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.OfFn

namespace BitDFT.LowMultiplierLemmas
open IntMul

theorem bin_succ (k z : ℕ) : bin (k+1) z = bin k (z/2) ++ [z.testBit 0] := by
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

theorem val_append_bit (w : List Bool) (b : Bool) : val (w++[b]) = 2*val w+b.toNat := by
  simp [val,List.foldl_append]

theorem low_bit (z : ℕ) : (z.testBit 0).toNat = z%2 := by
  have h := Nat.mod_lt z (by decide : 0 < 2)
  simp only [Nat.testBit_eq_decide_div_mod_eq,Nat.pow_zero,Nat.div_one]
  by_cases hz : z%2 = 1
  · simp [hz]
  · have h0 : z%2 = 0 := by omega
    simp [h0]

theorem val_bin (k z : ℕ) (hz : z < 2^k) : val (bin k z) = z := by
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

theorem canonical (n : ℕ) (hn : 1 ≤ n) :
    ∃ tail, bin n.size n = true::tail ∧ tail.length+1=n.size ∧ val (true::tail)=n := by
  have hs : 0 < n.size := Nat.size_pos.mpr (by omega)
  have hb : n.testBit (n.size-1) = true := by
    apply Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt
    · exact Nat.lt_size.mp (by omega)
    · simpa [Nat.sub_add_cancel hs] using Nat.lt_size_self n
  have hval := val_bin n.size n (Nat.lt_size_self n)
  have hlen : (bin n.size n).length = n.size := by simp [bin]
  cases he : bin n.size n with
  | nil => simp [he] at hlen; omega
  | cons b tail =>
    have hhead := congrArg (fun l : List Bool => l[0]?) he
    have hzero : n.size-1-0 = n.size-1 := by omega
    simp [bin,List.getElem?_ofFn,hs,hzero,hb] at hhead
    subst b
    refine ⟨tail,rfl,?_,?_⟩
    · simpa [he] using hlen
    · simpa [he] using hval

end BitDFT.LowMultiplierLemmas

open IntMul

/-- The actual supplied multiplier is called at q bits on both operands. -/
theorem solution (M : MultitapeTM) (q n a : ℕ) (T : ℝ)
    (hq : 1 ≤ q) (hn : n < 2^q) (ha : a ≤ 2^q) (hM : MultipliesAt M q T) :
    ∃ t : ℕ,
      (t : ℝ) ≤ 36*T ∧
      (IntMul.TrackedNativeCall.machine M).HaltsWithOutput
        (bin q n) (bin q (a%2^q)) t (bin (2*q) (n*(a%2^q))) ∧
      n*a = (if a.testBit q then n*2^q else n*(a%2^q)) := by
  have hlow : a%2^q < 2^q := Nat.mod_lt _ (by positivity)
  have hnval := BitDFT.LowMultiplierLemmas.val_bin q n hn
  have haval := BitDFT.LowMultiplierLemmas.val_bin q (a%2^q) hlow
  have hx : (bin q n).length = q := by simp [bin]
  have hy : (bin q (a%2^q)).length = q := by simp [bin]
  obtain ⟨t,ht,ho⟩ := BitDFT.clean_multiplier_call M q T hq hM (bin q n)
    (bin q (a%2^q)) hx hy
  refine ⟨t,ht,?_,?_⟩
  · simpa only [hnval,haval] using ho.1
  · exact (BitDFT.scalar_low_product_selection q a n ha).2.1
