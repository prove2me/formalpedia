-- Prove2me | solution 1 for Egrs75.ClearingP2.lowDigits_div_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:29:57.767852+00:00
-- url     : https://prove2.me/submissions/3a479b25-e033-476b-a406-96acb7131c28

module
public import Definitions.Def_LeanPool_Egrs75_Defs
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_RoundUp
public import Definitions.Def_LeanPool_Egrs75_AddBranch
public import Theorems.Thm_Egrs75_RepairPaperfaithful_lowDigits_iff_digitAt


set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.ClearingP2
open Nat
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful
namespace Egrs75.ClearingP2
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) {n m : ℕ}
    (hpn : LowDigits p n) : LowDigits p (n / p ^ m) := by
  rw [lowDigits_iff_digitAt hp] at hpn ⊢
  intro i
  -- digitAt p i (n / p^m) = (n / p^m) / p^i % p = n / p^(m+i) % p = digitAt p (m+i) n
  have hdiv : (n / p ^ m) / p ^ i = n / p ^ (m + i) := by
    rw [Nat.div_div_eq_div_mul, ← pow_add]
  have : digitAt p i (n / p ^ m) = digitAt p (m + i) n := by
    unfold digitAt; rw [hdiv]
  rw [this]; exact hpn (m + i)
end Egrs75.ClearingP2
