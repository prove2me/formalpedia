-- Prove2me | solution 1 for Egrs75.ClearingP3.sub_block_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:30:00.025105+00:00
-- url     : https://prove2.me/submissions/640312e5-b61f-4c3b-817d-b2b37d002291

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Mathlib.Data.Nat.Factorization.Defs
public import Definitions.Def_LeanPool_Egrs75_RoundUp
public import Definitions.Def_LeanPool_Egrs75_SubtractBranch
public import Theorems.Thm_Egrs75_ClearingP3_half_pred_pow_lt
public import Theorems.Thm_Egrs75_ClearingP3_sub_block_eq

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
    a * p ^ m - (p ^ m + 1) / 2 < p ^ (m + 1) := by
  rw [sub_block_eq hodd ha1]
  have hpm : 1 ≤ p ^ m := Nat.one_le_pow _ _ (by omega)
  have hH : (p ^ m - 1) / 2 < p ^ m := half_pred_pow_lt (by omega) m
  -- (a-1)*p^m + (p^m-1)/2 < (a-1)*p^m + p^m = a*p^m ≤ ((p-1)/2)*p^m < p*p^m = p^(m+1)
  have hahalf : a ≤ (p - 1) / 2 := haA
  have hhalflt : (p - 1) / 2 < p := by omega
  have hpmpos : 0 < p ^ m := by positivity
  have heq : (a - 1) * p ^ m + p ^ m = a * p ^ m := by
    have : (a - 1 + 1) * p ^ m = (a - 1) * p ^ m + p ^ m := by ring
    rw [← this]; congr 1; omega
  calc (a - 1) * p ^ m + (p ^ m - 1) / 2
      < (a - 1) * p ^ m + p ^ m := by omega
    _ = a * p ^ m := heq
    _ ≤ ((p - 1) / 2) * p ^ m := Nat.mul_le_mul_right _ hahalf
    _ < p * p ^ m := by
        simp_all
    _ = p ^ (m + 1) := by rw [pow_succ]; ring
end Egrs75.ClearingP3
