-- Prove2me | solution 1 for Egrs75.RoundUp.lowDigits_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:27:27.797826+00:00
-- url     : https://prove2.me/submissions/956f3139-2163-4143-8cfa-6ed3db8a06c8

module
public import Definitions.Def_LeanPool_Egrs75_Defs
public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Data.Finset.Attr
public import Definitions.Def_LeanPool_Egrs75_RoundUp
public import Theorems.Thm_Egrs75_RoundUp_lowDigits_zero

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.RoundUp
open Nat
open Egrs75
variable (p : ℕ)
namespace Egrs75.RoundUp
theorem _root_.solution {p m d : ℕ} (hp : 2 ≤ p) (hd : d ≤ (p - 1) / 2)
    (hm : LowDigits p m) : LowDigits p (p * m + d) := by
  have hp1 : 1 < p := by omega
  have hdp : d < p := by omega
  rcases eq_or_ne (p * m + d) 0 with h0 | h0
  · rw [show p * m + d = 0 from h0]; exact lowDigits_zero p
  · unfold LowDigits at hm ⊢
    -- digits p (p*m+d) = d :: digits p m   (since (p*m+d)%p = d, (p*m+d)/p = m)
    have hmod : (p * m + d) % p = d := by
      rw [Nat.mul_add_mod_self_left]; exact Nat.mod_eq_of_lt hdp
    have hdiv : (p * m + d) / p = m := by
      rw [Nat.mul_add_div (by omega : 0 < p), Nat.div_eq_of_lt hdp, Nat.add_zero]
    rw [Nat.digits_def' hp1 (Nat.pos_of_ne_zero h0), hmod, hdiv]
    simp_all
end Egrs75.RoundUp
