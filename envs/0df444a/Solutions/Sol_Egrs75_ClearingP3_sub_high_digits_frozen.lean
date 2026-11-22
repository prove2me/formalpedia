-- Prove2me | solution 1 for Egrs75.ClearingP3.sub_high_digits_frozen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:29:52.9237+00:00
-- url     : https://prove2.me/submissions/2d853071-c96d-4d5c-bbcc-99d648d2a722

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Mathlib.Data.Nat.Factorization.Defs
public import Definitions.Def_LeanPool_Egrs75_RoundUp
public import Definitions.Def_LeanPool_Egrs75_SubtractBranch
public import Theorems.Thm_Egrs75_ClearingP3_sub_div_pow_eq

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.ClearingP3
open Nat
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful
namespace Egrs75.ClearingP3
theorem _root_.solution {q n S j idx : ℕ} (hq : 0 < q) (hS : S ≤ n % q ^ j)
    (hidx : j ≤ idx) :
    (n - S) / q ^ idx % q = n / q ^ idx % q := by
  -- (n-S)/q^idx = ((n-S)/q^j)/q^(idx-j) = (n/q^j)/q^(idx-j) = n/q^idx
  have hpow : q ^ idx = q ^ j * q ^ (idx - j) := by rw [← pow_add]; congr 1; omega
  have hkey : (n - S) / q ^ idx = n / q ^ idx := by
    rw [hpow, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, sub_div_pow_eq hq hS]
  rw [hkey]
end Egrs75.ClearingP3
