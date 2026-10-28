-- Prove2me | solution 1 for BitDFT.bin_padding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T19:13:18.108437+00:00
-- url     : https://prove2.me/submissions/f5a4bfe7-7ede-4be8-9f2e-78baee4882e6

import Definitions.Def_IntMul_MultitapeModel
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bitwise
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

theorem solution (r s z : ℕ) (hz : z < 2^r) :
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