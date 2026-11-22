-- Prove2me | solution 1 for Egrs75.ConcreteMath.two_mul_padicValNat_three_centralBinom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:25:05.151241+00:00
-- url     : https://prove2.me/submissions/0457cb0f-5187-437b-adb7-2bb38ede9eae

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
theorem _root_.solution (n : ℕ) :
    2 * padicValNat 3 (Nat.centralBinom n) =
      2 * (Nat.digits 3 n).sum - (Nat.digits 3 (2 * n)).sum := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  have := sub_one_mul_padicValNat_centralBinom 3 n
  simpa using this
end Egrs75.ConcreteMath
