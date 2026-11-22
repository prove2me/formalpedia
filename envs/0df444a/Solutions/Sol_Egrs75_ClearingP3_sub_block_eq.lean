-- Prove2me | solution 1 for Egrs75.ClearingP3.sub_block_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:28:05.732964+00:00
-- url     : https://prove2.me/submissions/463186f0-cd48-41ee-babd-bb1e52ab0b97

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Mathlib.Data.Nat.Factorization.Defs
public import Definitions.Def_LeanPool_Egrs75_RoundUp
public import Definitions.Def_LeanPool_Egrs75_SubtractBranch

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
theorem _root_.solution {p : ℕ} (hodd : Odd p) {a m : ℕ} (ha : 1 ≤ a) :
    a * p ^ m - (p ^ m + 1) / 2 = (a - 1) * p ^ m + (p ^ m - 1) / 2 := by
  have hpm : 1 ≤ p ^ m := Nat.one_le_pow _ _ (by
    rcases hodd with ⟨k, hk⟩; omega)
  -- relate (p^m+1)/2 and (p^m-1)/2: 2·((p^m+1)/2) = p^m+1, 2·((p^m-1)/2)=p^m-1
  have hoddpow : Odd (p ^ m) := hodd.pow
  obtain ⟨k, hk⟩ := hoddpow
  -- p^m = 2k+1; (p^m+1)/2 = k+1, (p^m-1)/2 = k
  have hS : (p ^ m + 1) / 2 = k + 1 := by rw [hk]; omega
  have hH : (p ^ m - 1) / 2 = k := by rw [hk]; omega
  rw [hS, hH, hk]
  -- a*(2k+1) - (k+1) = (a-1)*(2k+1) + k
  cases a with
  | zero => omega
  | succ b =>
    -- (b+1)*(2k+1) - (k+1) = b*(2k+1) + k
    have : (b + 1) * (2 * k + 1) = b * (2 * k + 1) + (2 * k + 1) := by ring
    rw [this]; simp only [Nat.add_sub_cancel]; omega
end Egrs75.ClearingP3
