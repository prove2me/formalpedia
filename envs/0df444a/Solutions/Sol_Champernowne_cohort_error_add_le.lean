-- Prove2me | solution 1 for Champernowne.cohort_error_add_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:38:08.957751+00:00
-- url     : https://prove2.me/submissions/a5e39f51-7d6e-4bed-8ad8-22c1e7efbea4

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
theorem _root_.solution {b : ℕ} (hb : 1 < b) (c K : ℕ) :
    6 * c * b ^ K + 3 * c * b ^ (K + 1) ≤ 6 * c * b ^ (K + 1) := by
  rw [pow_succ']
  have hstep : c * b ^ K * 2 ≤ c * b ^ K * b := Nat.mul_le_mul_left _ hb
  nlinarith only [hstep]
end Champernowne
