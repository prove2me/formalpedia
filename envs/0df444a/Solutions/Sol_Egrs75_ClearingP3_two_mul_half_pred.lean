-- Prove2me | solution 1 for Egrs75.ClearingP3.two_mul_half_pred
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:29:59.139184+00:00
-- url     : https://prove2.me/submissions/7ec55a1b-90dd-4ac9-8b20-ae4274cc5356

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
theorem _root_.solution {p : ℕ} (hodd : Odd p) : 2 * ((p - 1) / 2) = p - 1 := by
  obtain ⟨k, hk⟩ := hodd
  simp_all
end Egrs75.ClearingP3
