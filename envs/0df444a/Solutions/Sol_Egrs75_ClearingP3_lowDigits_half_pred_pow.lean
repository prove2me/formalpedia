-- Prove2me | solution 1 for Egrs75.ClearingP3.lowDigits_half_pred_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:32:11.712283+00:00
-- url     : https://prove2.me/submissions/36b3a2b2-cbce-4318-adda-a168406ef686

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Mathlib.Data.Nat.Factorization.Defs
public import Definitions.Def_LeanPool_Egrs75_RoundUp
public import Definitions.Def_LeanPool_Egrs75_SubtractBranch
public import Theorems.Thm_Egrs75_ClearingP3_half_pred_pow_succ
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
theorem _root_.solution {p : ℕ} (hp : 3 ≤ p) (hodd : Odd p) (m : ℕ) :
    LowDigits p ((p ^ m - 1) / 2) := by
  induction m with
  | zero => simpa using RoundUp.lowDigits_zero p
  | succ k ih =>
    rw [half_pred_pow_succ (by omega) hodd k]
    exact RoundUp.lowDigits_cons (by omega) (le_refl _) ih
end Egrs75.ClearingP3
