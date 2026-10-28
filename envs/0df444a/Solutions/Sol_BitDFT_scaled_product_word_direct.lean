-- Prove2me | solution 1 for BitDFT.scaled_product_word_direct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T19:16:06.606905+00:00
-- url     : https://prove2.me/submissions/c5264ab3-51cf-4887-93e6-dd68b73814b3

import Definitions.Def_IntMul_MultitapeModel
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic
namespace BitDFT.LocalBinPadding
open IntMul

private theorem bin_head (q a : ℕ) : bin (q+1) a = a.testBit q :: bin q a := by
  unfold bin
  rw [List.ofFn_succ]
  congr 1
  congr 1
  funext i
  congr 1
  simp only [Fin.val_succ]
  omega

theorem bin_padding (r s z : ℕ) (hz : z < 2^r) :
    bin (r+s) z = List.replicate s false ++ bin r z := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hs : z < 2^(r+s) := by
      apply lt_of_lt_of_le hz
      apply Nat.pow_le_pow_right (by decide : 0 < 2)
      omega
    rw [show r+(s+1) = (r+s)+1 by omega,bin_head,Nat.testBit_eq_false_of_lt hs,ih]
    simp [List.replicate_succ, List.append_assoc]
end BitDFT.LocalBinPadding

open IntMul

/-- The low-product branch from the q-bit call is a prefix of the scaler's exact result width. -/
theorem solution (q n a : ℕ) (hq : lg n+1 ≤ q) (hn : n ≤ 2^lg n) (ha : a ≤ 2^q) :
    n*(a%2^q) < 2^(q+lg n+1) ∧
    bin (2*q) (n*(a%2^q)) =
      List.replicate (2*q-(q+lg n+1)) false ++ bin (q+lg n+1) (n*(a%2^q)) := by
  have hlow : a%2^q < 2^q := Nat.mod_lt _ (by positivity)
  have hprod : n*(a%2^q) < 2^(q+lg n) := by
    calc
      n*(a%2^q) ≤ 2^lg n*(a%2^q) := Nat.mul_le_mul_right _ hn
      _ < 2^lg n*2^q := Nat.mul_lt_mul_of_pos_left hlow (by positivity)
      _ = 2^(q+lg n) := by rw [pow_add,Nat.mul_comm]
  have hwidth : q+lg n+1 ≤ 2*q := by omega
  have hlt : n*(a%2^q) < 2^(q+lg n+1) := by
    have hp : 2^(q+lg n) < 2^(q+lg n+1) := by
      rw [pow_succ]
      omega
    omega
  refine ⟨hlt,?_⟩
  have hsum : (q+lg n+1)+(2*q-(q+lg n+1)) = 2*q := by omega
  rw [← hsum]
  have hp := BitDFT.LocalBinPadding.bin_padding (q+lg n+1) (2*q-(q+lg n+1))
    (n*(a%2^q)) hlt
  simpa [Nat.add_sub_cancel_left] using hp
