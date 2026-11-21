-- Prove2me | solution 1 for Champernowne.geomsum_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:39:33.065676+00:00
-- url     : https://prove2.me/submissions/d6d0e41c-857d-4eb4-a2a0-f7aad6e0352f

module
public import Definitions.Def_LeanPool_Champernowne_Count
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Champernowne_DigitCount

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution {b : ℕ} (hb : 1 < b) (K : ℕ) :
    ∑ i ∈ Finset.range K, b ^ i < b ^ K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have h2 : b ^ K * 2 ≤ b ^ K * b := Nat.mul_le_mul_left _ hb
    omega
end Champernowne
