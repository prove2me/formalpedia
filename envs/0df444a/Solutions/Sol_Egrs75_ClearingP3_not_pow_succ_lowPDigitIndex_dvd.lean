-- Prove2me | solution 1 for Egrs75.ClearingP3.not_pow_succ_lowPDigitIndex_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:29:58.67531+00:00
-- url     : https://prove2.me/submissions/50486170-081b-423c-ab36-b1a0665a1dd7

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
theorem _root_.solution {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    ¬ p ^ (lowPDigitIndex p n + 1) ∣ n := by
  unfold lowPDigitIndex
  have : Fact p.Prime := ⟨hp⟩
  exact Nat.pow_succ_factorization_not_dvd hn hp
end Egrs75.ClearingP3
