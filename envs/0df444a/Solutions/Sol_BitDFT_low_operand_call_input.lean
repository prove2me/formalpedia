-- Prove2me | solution 1 for BitDFT.low_operand_call_input
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T00:23:33.865388+00:00
-- url     : https://prove2.me/submissions/ffd68261-769b-4b3e-84f0-bbdbab90216f

import Theorems.Thm_BitDFT_low_operand_copy_correct
import Definitions.Def_BitDFT_Encoding
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bitwise

set_option autoImplicit false
open BitDFT BitDFT.LowOperandCopy IntMul

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
  simp [Nat.testBit_mod_two_pow, hi]

/-- The copier's output tape is exactly the low q-bit operand required by the
    clean multiplier call, including the boundary magnitude 2^q. -/
theorem solution (q : ℕ) (z : ℤ) :
    encInt (q+1) z = decide (z < 0) :: (z.natAbs).testBit q ::
      bin q (z.natAbs % 2^q) ∧
    (∃ t : ℕ, t ≤ q+5 ∧
      (machine (show sourceTape ≠ counterTape from by decide)).step^[t]
        (initial (show sourceTape ≠ counterTape from by decide)
          (decide (z < 0)) ((z.natAbs).testBit q) (bin q (z.natAbs % 2^q))) =
        final (show sourceTape ≠ counterTape from by decide)
          (decide (z < 0)) ((z.natAbs).testBit q) (bin q (z.natAbs % 2^q))) ∧
    (final (show sourceTape ≠ counterTape from by decide)
      (decide (z < 0)) ((z.natAbs).testBit q) (bin q (z.natAbs % 2^q))).cells
        ⟨1, by simp [storage]⟩ =
      storage.tapeOf ((bin q (z.natAbs % 2^q)).map storage.bitSym) := by
  let h : sourceTape ≠ counterTape := by decide
  let sign : Bool := decide (z < 0)
  let mag := z.natAbs
  let high := mag.testBit q
  let bits := bin q (mag % 2^q)
  have hbitslen : bits.length = q := by simp [bits, bin]
  have hword : encInt (q+1) z = sign :: high :: bits := by
    simp [encInt, sign, mag, high, bits, bin_head, bin_mod]
  obtain ⟨t, ht, hrun⟩ := BitDFT.low_operand_copy_correct h sign high bits
  constructor
  · exact hword
  constructor
  · exact ⟨t, by rw [hbitslen] at ht; omega, hrun⟩
  · change (finalBase sign high bits).cells
        ⟨1, by simp [storage]⟩ = storage.tapeOf (bits.map storage.bitSym)
    simp [finalBase, storage, SuffixCopyTwoTape.machine]
