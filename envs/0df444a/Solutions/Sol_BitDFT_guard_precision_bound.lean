-- Prove2me | solution 1 for BitDFT.guard_precision_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T12:02:45.245852+00:00
-- url     : https://prove2.me/submissions/c70b4405-ff83-4ac6-991d-274a8a7b7048

import Definitions.Def_BitDFT_Numerics
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
set_option autoImplicit false
noncomputable section
open BitDFT

theorem solution (n b : ℕ) (_hn : 1 ≤ n) :
    12 * n ^ 3 * 2 ^ b < 2 ^ guardPrecision n b := by
  have hn' : n ≤ 2 ^ IntMul.lg n :=
    (Nat.le_pow_clog (by decide : 1 < 2) n).trans
      (Nat.pow_le_pow_right (by decide : 0 < 2) (le_max_left _ _))
  have hc : n ^ 3 ≤ (2 ^ IntMul.lg n) ^ 3 := Nat.pow_le_pow_left hn' 3
  have hpos : 0 < (2 ^ IntMul.lg n) ^ 3 * 2 ^ b := by positivity
  calc
    12 * n ^ 3 * 2 ^ b ≤ 12 * (2 ^ IntMul.lg n) ^ 3 * 2 ^ b :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hc)
    _ < 32 * (2 ^ IntMul.lg n) ^ 3 * 2 ^ b := by nlinarith
    _ = 2 ^ guardPrecision n b := by
      simp only [guardPrecision, pow_add, Nat.mul_comm 3 (IntMul.lg n), pow_mul]
      ring

#print axioms solution
