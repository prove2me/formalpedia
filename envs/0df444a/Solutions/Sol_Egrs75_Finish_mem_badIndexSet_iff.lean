-- Prove2me | solution 1 for Egrs75.Finish.mem_badIndexSet_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:29:00.063185+00:00
-- url     : https://prove2.me/submissions/0cbe23df-571c-4f4b-b4d0-6b7742adb0cc

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
theorem _root_.solution {q n i : ℕ} (hq : 1 < q) :
    i ∈ badIndexSet q n ↔ BadAt q i n := by
  unfold BadAt digitAt badIndexSet
  simp only [Finset.mem_filter, Finset.mem_range, bigQ, decide_eq_true_eq]
  constructor
  · rintro ⟨_, hbig⟩
    -- in range: getD = n/q^i%q via getD_digits
    rwa [getD_digits n i (by omega)] at hbig
  · intro hbig
    -- bad ⟹ digit nonzero ⟹ index in range
    have hlen : i < (Nat.digits q n).length := by
      by_contra hcon
      push Not at hcon
      rw [← getD_digits n i (by omega), List.getD_eq_default _ 0 hcon] at hbig
      omega
    refine ⟨hlen, ?_⟩
    rwa [getD_digits n i (by omega)]
end Egrs75.Finish
