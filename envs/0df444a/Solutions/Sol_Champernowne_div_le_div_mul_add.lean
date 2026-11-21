-- Prove2me | solution 1 for Champernowne.div_le_div_mul_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:39:32.585458+00:00
-- url     : https://prove2.me/submissions/4896ed6e-ed87-4e7c-8213-6101eb485a3d

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
theorem _root_.solution (t p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    t / q ≤ t / (p * q) * p + p := by
  have hpq : 0 < p * q := Nat.mul_pos hp hq
  have e := Nat.div_add_mod t (p * q)
  have hm : t % (p * q) < p * q := Nat.mod_lt t hpq
  have key : t < (t / (p * q) * p + p) * q := by
    have h1 : t < p * q * (t / (p * q)) + p * q := by omega
    calc t < p * q * (t / (p * q)) + p * q := h1
    _ = (t / (p * q) * p + p) * q := by ring
  exact Nat.le_of_lt_succ (Nat.lt_succ_of_lt
    ((Nat.div_lt_iff_lt_mul hq).mpr key))
end Champernowne
