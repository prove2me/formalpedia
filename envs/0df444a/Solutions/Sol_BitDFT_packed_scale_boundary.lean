-- Prove2me | solution 1 for BitDFT.packed_scale_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T02:24:55.268644+00:00
-- url     : https://prove2.me/submissions/4251832b-ea0b-4963-98d5-01d3aae19817

import Definitions.Def_BitDFT_PackedScale
import Mathlib.Tactic

set_option autoImplicit false
open IntMul BitDFT.PackedScale

/-- The allowed boundary magnitude `2^q` still fits strictly inside half of
    the `2^(3q)` balanced packed base after scaling by any `n ≤ 2^q`. -/
theorem solution (n q ell : ℕ) (hn : n ≤ 2^ell)
    (hell : ell ≤ q) (hq : 2 ≤ q)
    (xs : List ℤ) (hxs : ∀ x ∈ xs, x.natAbs ≤ 2^q) :
    ∀ x ∈ xs, ((n : ℤ) * x).natAbs < 2^(3*q-1) := by
  have hp : 2^ell ≤ 2^q := Nat.pow_le_pow_right (by omega) hell
  have hnq : n ≤ 2^q := hn.trans hp
  have hexp : 2*q < 3*q-1 := by omega
  have hpow : 2^(2*q) < 2^(3*q-1) :=
    Nat.pow_lt_pow_right (by decide : 1 < 2) hexp
  intro x hx
  have hprod : n * x.natAbs ≤ 2^(2*q) := by
    calc
      n * x.natAbs ≤ 2^q * 2^q := Nat.mul_le_mul hnq (hxs x hx)
      _ = 2^(2*q) := by rw [← pow_add, show q + q = 2*q by omega]
  calc
    ((n : ℤ) * x).natAbs = n * x.natAbs := by
      rw [Int.natAbs_mul]
      simp
    _ ≤ 2^(2*q) := hprod
    _ < 2^(3*q-1) := hpow
