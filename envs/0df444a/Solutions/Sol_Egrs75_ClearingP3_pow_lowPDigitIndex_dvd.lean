-- Prove2me | solution 1 for Egrs75.ClearingP3.pow_lowPDigitIndex_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:27:52.781121+00:00
-- url     : https://prove2.me/submissions/0e2663b2-da90-4170-9351-f299716fc049

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
theorem _root_.solution {p n : ℕ} (_hp : 1 < p) (_hn : n ≠ 0) :
    p ^ (lowPDigitIndex p n) ∣ n := by
  unfold lowPDigitIndex
  exact Nat.ordProj_dvd n p
end Egrs75.ClearingP3
