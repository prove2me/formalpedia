-- Prove2me | solution 1 for BitDFT.scalar_low_operand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T19:07:50.339991+00:00
-- url     : https://prove2.me/submissions/dc2821d6-2f3d-4b05-82b0-9ed6f37ae9dd

import Definitions.Def_BitDFT_Encoding
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bitwise
open BitDFT IntMul

private theorem bin_head (q a : ℕ) : bin (q+1) a = a.testBit q :: bin q a := by
  unfold bin
  rw [List.ofFn_succ]
  congr 1
  congr 1
  funext i
  congr 1
  simp only [Fin.val_succ]
  omega

private theorem bin_mod (q a : ℕ) : bin q (a % 2^q) = bin q a := by
  unfold bin
  congr 1
  funext i
  have hi : q-1-i.val < q := by have := i.isLt; omega
  simp [Nat.testBit_mod_two_pow,hi]

/-- After skipping the sign and high magnitude bit, the scratch word is a valid q-bit operand. -/
theorem solution (q : ℕ) (z : ℤ) :
    (encInt (q+1) z).drop 2 = bin q (z.natAbs % 2^q) ∧
    ((encInt (q+1) z).drop 2).length = q ∧
    z.natAbs % 2^q < 2^q := by
  have he : (encInt (q+1) z).drop 2 = bin q (z.natAbs % 2^q) := by
    simp [encInt,bin_head,bin_mod]
  refine ⟨he,?_,Nat.mod_lt _ (Nat.two_pow_pos q)⟩
  rw [he]
  simp [bin]
