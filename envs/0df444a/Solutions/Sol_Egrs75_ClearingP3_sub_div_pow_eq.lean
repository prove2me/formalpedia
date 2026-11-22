-- Prove2me | solution 1 for Egrs75.ClearingP3.sub_div_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:28:40.247682+00:00
-- url     : https://prove2.me/submissions/7957c572-024f-46e5-9c10-0c8edfed63e4

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
theorem _root_.solution {q n S k : ℕ} (hq : 0 < q) (hS : S ≤ n % q ^ k) :
    (n - S) / q ^ k = n / q ^ k := by
  -- n = n % q^k + q^k * (n/q^k); n - S = (n%q^k - S) + q^k*(n/q^k), with n%q^k - S < q^k.
  have hqk : 0 < q ^ k := by positivity
  have hmod : n % q ^ k < q ^ k := Nat.mod_lt _ hqk
  -- abstract the mod and div as opaque naturals so the rewrite of `n` does not recurse
  set r := n % q ^ k with hr
  set d := n / q ^ k with hd
  have hdecomp : n = r + q ^ k * d := by rw [hr, hd]; exact (Nat.mod_add_div n _).symm
  have hsub : n - S = (r - S) + q ^ k * d := by omega
  rw [hsub, Nat.add_mul_div_left _ _ hqk, Nat.div_eq_of_lt (by omega), Nat.zero_add]
end Egrs75.ClearingP3
