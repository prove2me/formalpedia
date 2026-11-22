-- Prove2me | solution 1 for Egrs75.ClearingP3.mod_pow_succ_lowPDigitIndex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:30:14.355472+00:00
-- url     : https://prove2.me/submissions/c93c498d-e31c-458a-a548-0233744cfd83

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Mathlib.Data.Nat.Factorization.Defs
public import Definitions.Def_LeanPool_Egrs75_RoundUp
public import Definitions.Def_LeanPool_Egrs75_SubtractBranch
public import Theorems.Thm_Egrs75_ClearingP3_mod_pow_lowPDigitIndex

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
theorem _root_.solution {p n : ℕ} (hp : 1 < p) (hn : n ≠ 0) :
    n % p ^ (lowPDigitIndex p n + 1)
      = (n / p ^ (lowPDigitIndex p n) % p) * p ^ (lowPDigitIndex p n) := by
  set m := lowPDigitIndex p n with hm
  -- Nat.mod_mul : n % (p^m * p) = n % p^m + p^m * (n / p^m % p)
  have hmod0 : n % p ^ m = 0 := mod_pow_lowPDigitIndex hp hn
  have hpow : p ^ (m + 1) = p ^ m * p := by rw [pow_succ]
  rw [hpow, Nat.mod_mul, hmod0, Nat.zero_add, Nat.mul_comm]
end Egrs75.ClearingP3
