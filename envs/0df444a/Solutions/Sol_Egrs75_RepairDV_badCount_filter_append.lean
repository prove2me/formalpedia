-- Prove2me | solution 1 for Egrs75.RepairDV.badCount_filter_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:31:30.708906+00:00
-- url     : https://prove2.me/submissions/6a166dfb-3ee9-44d4-89f3-d83a83e072bf

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
theorem _root_.solution (q : ℕ) (L₁ L₂ : List ℕ) :
    ((L₁ ++ L₂).filter (fun d => bigQ q d)).length =
      (L₁.filter (fun d => bigQ q d)).length + (L₂.filter (fun d => bigQ q d)).length := by
  rw [List.filter_append, List.length_append]
end Egrs75.RepairDV
