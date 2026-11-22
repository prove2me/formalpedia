-- Prove2me | solution 1 for Egrs75.ClearingP3.two_mul_half_pred_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:30:59.324019+00:00
-- url     : https://prove2.me/submissions/55db6aae-190a-48b8-bbb3-36d681a6e28d

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
theorem _root_.solution {p : ℕ} (hodd : Odd p) (m : ℕ) :
    2 * ((p ^ m - 1) / 2) = p ^ m - 1 := by
  have hoddpow : Odd (p ^ m) := hodd.pow
  obtain ⟨k, hk⟩ := hoddpow
  simp_all
end Egrs75.ClearingP3
