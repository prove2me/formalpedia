-- Prove2me | solution 1 for Egrs75.ClearingP3.half_pred_pow_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:31:36.521992+00:00
-- url     : https://prove2.me/submissions/c0b3bc36-4bc9-4825-b44e-d4a0f46afed9

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Mathlib.Data.Nat.Factorization.Defs
public import Definitions.Def_LeanPool_Egrs75_RoundUp
public import Definitions.Def_LeanPool_Egrs75_SubtractBranch
public import Theorems.Thm_Egrs75_ClearingP3_two_mul_half_pred
public import Theorems.Thm_Egrs75_ClearingP3_two_mul_half_pred_pow

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
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) (hodd : Odd p) (m : ℕ) :
    (p ^ (m + 1) - 1) / 2 = p * ((p ^ m - 1) / 2) + (p - 1) / 2 := by
  -- double both sides and divide; everything even.
  have h1 : 2 * ((p ^ (m + 1) - 1) / 2) = p ^ (m + 1) - 1 := two_mul_half_pred_pow hodd (m + 1)
  have h2 : 2 * ((p ^ m - 1) / 2) = p ^ m - 1 := two_mul_half_pred_pow hodd m
  have h3 : 2 * ((p - 1) / 2) = p - 1 := two_mul_half_pred hodd
  have hppos : 1 ≤ p ^ m := Nat.one_le_pow _ _ (by omega)
  -- 2 * RHS = 2p·((p^m-1)/2) + 2·((p-1)/2) = p·(p^m-1) + (p-1) = p^(m+1) - 1 = 2 * LHS
  have hkey : 2 * (p * ((p ^ m - 1) / 2) + (p - 1) / 2) = p ^ (m + 1) - 1 := by
    have hexpand : 2 * (p * ((p ^ m - 1) / 2) + (p - 1) / 2)
        = p * (2 * ((p ^ m - 1) / 2)) + 2 * ((p - 1) / 2) := by ring
    rw [hexpand, h2, h3]
    -- goal: p * (p^m - 1) + (p - 1) = p^(m+1) - 1
    -- p*(p^m-1) = p*p^m - p = p^(m+1) - p; +(p-1) = p^(m+1) - 1
    have hpm1 : p ≤ p ^ (m + 1) := by
      calc p = p * 1 := by ring
        _ ≤ p * p ^ m := Nat.mul_le_mul_left p hppos
        _ = p ^ (m + 1) := by rw [pow_succ]; ring
    have hmuls : p * (p ^ m - 1) = p ^ (m + 1) - p := by
      rw [Nat.mul_sub, Nat.mul_one, pow_succ]; ring_nf
    rw [hmuls]
    omega
  omega
end Egrs75.ClearingP3
