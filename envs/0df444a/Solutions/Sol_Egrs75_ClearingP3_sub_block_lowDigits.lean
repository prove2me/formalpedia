-- Prove2me | solution 1 for Egrs75.ClearingP3.sub_block_lowDigits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:32:46.087342+00:00
-- url     : https://prove2.me/submissions/9436c378-0140-47a2-82ec-fe1b1644ab2c

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Mathlib.Data.Nat.Factorization.Defs
public import Definitions.Def_LeanPool_Egrs75_RoundUp
public import Definitions.Def_LeanPool_Egrs75_SubtractBranch
public import Theorems.Thm_Egrs75_ClearingP3_lowDigits_half_pred_pow
public import Theorems.Thm_Egrs75_ClearingP3_half_pred_pow_lt
public import Theorems.Thm_Egrs75_ClearingP3_sub_block_eq
public import Theorems.Thm_Egrs75_RepairDV_lowDigits_disjoint_add
public import Theorems.Thm_Egrs75_RoundUp_lowDigits_cons
public import Theorems.Thm_Egrs75_RoundUp_lowDigits_zero


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
theorem _root_.solution {p : ℕ} (hp : 3 ≤ p) (hodd : Odd p) {a m : ℕ}
    (ha1 : 1 ≤ a) (haA : a ≤ (p - 1) / 2) :
    LowDigits p (a * p ^ m - (p ^ m + 1) / 2) := by
  rw [sub_block_eq hodd ha1]
  -- (a-1)*p^m + (p^m-1)/2 = (p^m-1)/2 + p^m * (a-1)
  have hcomm : (a - 1) * p ^ m + (p ^ m - 1) / 2 = (p ^ m - 1) / 2 + p ^ m * (a - 1) := by
    ring
  rw [hcomm]
  rcases Nat.eq_zero_or_pos (a - 1) with ha0 | hapos
  · -- a = 1: block = (p^m-1)/2, already LowDigits
    rw [ha0, Nat.mul_zero, Nat.add_zero]
    exact lowDigits_half_pred_pow hp hodd m
  · -- a ≥ 2: disjoint add, U = (p^m-1)/2 < p^m, Hi = a-1 > 0, both LowDigits
    apply lowDigits_disjoint_add (by omega) (half_pred_pow_lt (by omega) m) hapos
      (lowDigits_half_pred_pow hp hodd m)
    -- LowDigits p (a-1): single digit a-1 ≤ (p-1)/2
    have h : a - 1 = p * 0 + (a - 1) := by ring
    rw [h]
    exact RoundUp.lowDigits_cons (by omega) (by omega) (RoundUp.lowDigits_zero p)
end Egrs75.ClearingP3
