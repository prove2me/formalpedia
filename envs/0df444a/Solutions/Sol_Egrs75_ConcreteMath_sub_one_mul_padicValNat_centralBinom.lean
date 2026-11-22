-- Prove2me | solution 1 for Egrs75.ConcreteMath.sub_one_mul_padicValNat_centralBinom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:24:36.80797+00:00
-- url     : https://prove2.me/submissions/52b8da9c-d69f-4ccc-b9c9-25e49303b79e

module
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.MaxPowDiv
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Definitions.Def_LeanPool_Egrs75_KummerValuation

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.ConcreteMath
open Nat
namespace Egrs75.ConcreteMath
theorem _root_.solution (p : ℕ) [hp : Fact p.Prime] (n : ℕ) :
    (p - 1) * padicValNat p (Nat.centralBinom n) =
      2 * (Nat.digits p n).sum - (Nat.digits p (2 * n)).sum := by
  rw [Nat.centralBinom_eq_two_mul_choose]
  have hk : n ≤ 2 * n := Nat.le_mul_of_pos_left n (by decide)
  have hkummer :
      (p - 1) * padicValNat p ((2 * n).choose n) =
        (Nat.digits p n).sum + (Nat.digits p (2 * n - n)).sum -
          (Nat.digits p (2 * n)).sum :=
    sub_one_mul_padicValNat_choose_eq_sub_sum_digits (p := p) (k := n)
      (n := 2 * n) hk
  have h2n : 2 * n - n = n := by omega
  rw [h2n] at hkummer
  rw [hkummer]
  ring_nf
end Egrs75.ConcreteMath
