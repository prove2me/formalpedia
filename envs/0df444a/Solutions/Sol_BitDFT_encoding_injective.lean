-- Prove2me | solution 1 for BitDFT.encoding_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T12:30:02.116091+00:00
-- url     : https://prove2.me/submissions/a5347650-155b-48ea-9b8c-c1ad53bc5f59

import Definitions.Def_BitDFT_Encoding
import Mathlib.Data.Nat.Bitwise
set_option autoImplicit false
open BitDFT

theorem solution (w : ℕ) (a b : ℤ)
    (ha : a.natAbs < 2 ^ w) (hb : b.natAbs < 2 ^ w)
    (h : encInt w a = encInt w b) : a = b := by
  have hh : decide (a < 0) = decide (b < 0) ∧ IntMul.bin w a.natAbs = IntMul.bin w b.natAbs := by
    simpa [encInt] using h
  have habs : a.natAbs = b.natAbs := by
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < w
    · have he := congrArg (fun l : List Bool => l[w - 1 - i]?) hh.2
      have hj : w - 1 - i < w := by omega
      have hij : w - 1 - (w - 1 - i) = i := by omega
      simpa [IntMul.bin, List.getElem?_ofFn, hj, hij] using he
    · have hp : 2^w ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.testBit_eq_false_of_lt (ha.trans_le hp), Nat.testBit_eq_false_of_lt (hb.trans_le hp)]
  have hsign : (a < 0 ↔ b < 0) := by
    by_cases ha0 : a < 0 <;> by_cases hb0 : b < 0 <;> simp_all <;> omega
  rcases Int.natAbs_eq a with ha' | ha' <;>
    rcases Int.natAbs_eq b with hb' | hb' <;> omega
