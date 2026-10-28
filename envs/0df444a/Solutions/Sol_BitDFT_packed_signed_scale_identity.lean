-- Prove2me | solution 1 for BitDFT.packed_signed_scale_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T02:29:35.549976+00:00
-- url     : https://prove2.me/submissions/1ed1397b-6a88-4b83-84fe-b353a348dd8c

import Definitions.Def_IntMul_HvdH_KronMul
import Mathlib.Tactic

set_option autoImplicit false
open IntMul IntMul.HvdH

/-- Scale a signed Kronecker-packed block by multiplying its packed integer.
    The coefficient bound is inclusive at 2^q, matching the DFT disc bound. -/
theorem solution (n q ell : ℕ) (hn : n ≤ 2^ell)
    (hell : ell ≤ q) (hq : 2 ≤ q)
    (xs : List ℤ) (hxs : ∀ x ∈ xs, x.natAbs ≤ 2^q) :
    (∀ x ∈ xs, ((n : ℤ) * x).natAbs < 2^(3*q-1)) ∧
      kpack (2^(3*q)) (xs.map (fun x => (n : ℤ) * x)) =
        (n : ℤ) * kpack (2^(3*q)) xs := by
  constructor
  · have hp : 2^ell ≤ 2^q := Nat.pow_le_pow_right (by omega) hell
    have hnq : n ≤ 2^q := hn.trans hp
    have hexp : 2*q < 3*q-1 := by omega
    have hpow : 2^(2*q) < 2^(3*q-1) :=
      Nat.pow_lt_pow_right (by decide : 1 < 2) hexp
    intro x hx
    have hprod : n * x.natAbs ≤ 2^(2*q) := by
      calc
        n * x.natAbs ≤ 2^q * 2^q := Nat.mul_le_mul hnq (hxs x hx)
        _ = 2^(2*q) := by rw [← pow_add, show q+q=2*q by omega]
    calc
      ((n : ℤ) * x).natAbs = n * x.natAbs := by rw [Int.natAbs_mul]; simp
      _ ≤ 2^(2*q) := hprod
      _ < 2^(3*q-1) := hpow
  · induction xs with
    | nil => rfl
    | cons x xs ih =>
        have htail : ∀ z ∈ xs, z.natAbs ≤ 2^q := by
          intro z hz
          exact hxs z (by simp [hz])
        simp only [List.map_cons, kpack]
        rw [ih htail]
        ring
