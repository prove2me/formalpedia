-- Prove2me | solution 1 for Egrs75.Finish.two_pow_top_le_badPrefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:40:30.684846+00:00
-- url     : https://prove2.me/submissions/07c07319-6aef-4f46-9ff9-34960d3c31a9

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Definitions.Def_LeanPool_Egrs75_ClearingHigh
public import Definitions.Def_LeanPool_Egrs75_MuFinish
public import Definitions.Def_LeanPool_Egrs75_Reduction
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Nat.Totient
public import Definitions.Def_LeanPool_Egrs75_BadPrefixRoute
public import Theorems.Thm_Egrs75_Finish_topBadIndex_mem_set

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.Finish
open Nat
open Finset
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful
open Egrs75.Probe
namespace Egrs75.Finish
theorem _root_.solution {q n : ℕ} (hq : 1 < q) (hbad : 0 < badCountQ q n) :
    2 ^ (topBadIndex q n) ≤ badPrefix q n := by
  unfold badPrefix
  exact Finset.single_le_sum (f := fun i => 2 ^ i) (fun i _ => Nat.zero_le _)
    (topBadIndex_mem_set hq hbad)
end Egrs75.Finish
