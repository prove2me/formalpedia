-- Prove2me | solution 2 for BitDFT.encoding_injective
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T12:30:56.448623+00:00
-- url     : https://prove2.me/submissions/abf34636-3a64-4f88-b966-5e7d874d9ad5

import Definitions.Def_BitDFT_Numerics
import Definitions.Def_IntMul_HvdH_KronMul
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open BitDFT

theorem solution (w : ℕ) (a b : ℤ)
    (ha : a.natAbs < 2 ^ w) (hb : b.natAbs < 2 ^ w)
    (h : encInt w a = encInt w b) : a = b := by
  simp only [encInt, List.singleton_append, List.cons.injEq] at h
  obtain ⟨hs, hbin⟩ := h
  have hab : a.natAbs = b.natAbs := by
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < w
    · have := congrArg (fun l => l[w - 1 - i]?) hbin
      simp only [IntMul.bin, List.getElem?_ofFn] at this
      have hlt : w - 1 - i < w := by omega
      simp [hlt] at this
      have he : w - 1 - (w - 1 - i) = i := by omega
      rw [he] at this
      exact this
    · push_neg at hi
      rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) hi)),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) hi))]
  have hs' : (a < 0) ↔ (b < 0) := by simpa using hs
  rcases Int.natAbs_eq a with h1 | h1 <;> rcases Int.natAbs_eq b with h2 | h2 <;> omega
