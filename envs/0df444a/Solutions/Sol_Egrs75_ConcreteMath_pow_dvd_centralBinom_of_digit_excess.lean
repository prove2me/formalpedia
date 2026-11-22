-- Prove2me | solution 1 for Egrs75.ConcreteMath.pow_dvd_centralBinom_of_digit_excess
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:25:04.712237+00:00
-- url     : https://prove2.me/submissions/7c65334b-9f40-442e-bac8-cfc3f2d14338

module
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.MaxPowDiv
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Definitions.Def_LeanPool_Egrs75_KummerValuation
public import Theorems.Thm_Egrs75_ConcreteMath_sub_one_mul_padicValNat_centralBinom

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.ConcreteMath
open Nat
namespace Egrs75.ConcreteMath
theorem _root_.solution
    {p n m : ℕ} [hp : Fact p.Prime]
    (h : (p - 1) * m ≤
      2 * (Nat.digits p n).sum - (Nat.digits p (2 * n)).sum) :
    p ^ m ∣ Nat.centralBinom n := by
  have hform := sub_one_mul_padicValNat_centralBinom p n
  rw [← hform] at h
  have hp1 : 1 ≤ p - 1 := by
    have := hp.out.one_lt
    omega
  have hpos : 0 < p - 1 := hp1
  have hval : m ≤ padicValNat p (Nat.centralBinom n) :=
    Nat.le_of_mul_le_mul_left h hpos
  exact dvd_trans (pow_dvd_pow p hval) pow_padicValNat_dvd
end Egrs75.ConcreteMath
