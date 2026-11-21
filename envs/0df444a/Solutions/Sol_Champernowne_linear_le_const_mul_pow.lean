-- Prove2me | solution 1 for Champernowne.linear_le_const_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:38:03.730524+00:00
-- url     : https://prove2.me/submissions/ff2d6379-7d56-455d-af15-531b7e8e89a2

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
theorem _root_.solution {b : ℕ} (hb : 1 < b) (c j : ℕ) :
    c + j + 1 ≤ (c + 1) * b ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hpow : b ^ (j + 1) = b * b ^ j := by rw [pow_succ']
    rw [hpow]
    have h2 : (c + 1) * b ^ j * 2 ≤ (c + 1) * b ^ j * b := Nat.mul_le_mul_left _ hb
    nlinarith [ih]
end Champernowne
