-- Prove2me | solution 1 for Egrs75.RoundUp.lowDigits_ru
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:30:59.871608+00:00
-- url     : https://prove2.me/submissions/a86d441c-98f9-4436-a78e-3604a4e5cac1

module
public import Definitions.Def_LeanPool_Egrs75_Defs
public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Data.Finset.Attr
public import Definitions.Def_LeanPool_Egrs75_RoundUp
public import Theorems.Thm_Egrs75_RoundUp_lowDigits_zero
public import Theorems.Thm_Egrs75_RoundUp_lowDigits_cons
public import Theorems.Thm_Egrs75_RoundUp_lowDigits_one

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.RoundUp
open Nat
open Egrs75
variable (p : ℕ)
namespace Egrs75.RoundUp
theorem _root_.solution {p : ℕ} (hp : 3 ≤ p) (x : ℕ) : LowDigits p (ru p x) := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    rw [ru]
    split_ifs with hx0 hsmall hlow hlow2
    · exact lowDigits_zero p
    · -- x ≤ (p-1)/2 : single low digit, x = p*0 + x  (hlow : x ≤ (p-1)/2)
      have h : x = p * 0 + x := by ring
      rw [h]
      exact lowDigits_cons (by omega) hlow (lowDigits_zero p)
    · -- carry to p : p = p*1 + 0
      have hpc : LowDigits p (p * 1 + 0) :=
        lowDigits_cons (by omega) (Nat.zero_le _) (lowDigits_one hp)
      simpa using hpc
    · -- keep low digit:  p * ru (x/p) + x%p,  x%p ≤ (p-1)/2
      exact lowDigits_cons (by omega) hlow2 (ih (x / p) (Nat.div_lt_self (by omega) (by omega)))
    · -- carry branch:  p * ru (x/p + 1) = p * ru (x/p + 1) + 0
      have hdec : x / p + 1 < x := by
        have hdiv : x / p ≤ x / 3 := Nat.div_le_div_left hp (by omega)
        omega
      have hcarry : LowDigits p (p * ru p (x / p + 1) + 0) :=
        lowDigits_cons (by omega) (Nat.zero_le _) (ih (x / p + 1) hdec)
      simpa using hcarry
end Egrs75.RoundUp
