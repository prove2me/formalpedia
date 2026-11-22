-- Prove2me | solution 1 for Egrs75.RepairDV.badCount_filter_replicate_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:31:32.254762+00:00
-- url     : https://prove2.me/submissions/06acebb9-5598-4dd7-a4f6-ceb7fdedc114

module
public import Definitions.Def_LeanPool_Egrs75_LeafInduction
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Digits.Lemmas
public import Definitions.Def_LeanPool_Egrs75_DigitVector

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.RepairDV
open Nat
open Egrs75
open Egrs75.LeafInduction
namespace Egrs75.RepairDV
theorem _root_.solution (q k : ℕ) :
    ((List.replicate k 0).filter (fun d => bigQ q d)).length = 0 := by
  simp_all
end Egrs75.RepairDV
