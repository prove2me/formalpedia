-- Prove2me | solution 1 for Champernowne.length_bigDigits_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:35:29.646256+00:00
-- url     : https://prove2.me/submissions/4ad53bc3-f306-42dd-b643-bb1073f05822

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
theorem _root_.solution {b m n : ℕ} (hb : 1 < b)
    (h1 : b ^ (m - 1) ≤ n) (h2 : n < b ^ m) :
    (bigDigits b n).length = m := by
  have hle : (Nat.digits b n).length ≤ m :=
    (Nat.digits_length_le_iff hb n).mpr h2
  have hlt : m - 1 < (Nat.digits b n).length :=
    (Nat.lt_digits_length_iff hb n).mpr h1
  simp only [bigDigits, List.length_reverse]
  omega
end Champernowne
